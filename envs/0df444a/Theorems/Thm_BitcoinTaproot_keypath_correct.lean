-- Prove2me | Theorems.Thm_BitcoinTaproot_keypath_correct
-- name    : BitcoinTaproot.keypath_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:37:30.781703+00:00
-- url     : https://prove2.me/theorems/dcae42fb-120c-44a7-90e0-f9d7082cc116
-- title:
--   Taproot key-path spending is correct
-- statement:
--   For every list of spent outputs, context $c$ (flags, transaction, input index, amount), signature and 32-byte output key $q$:
--   $$\mathrm{taprootHandler}(spent, c, [sig], q) = \mathtt{true} \iff \exists\, body\ ht\ h.\ |body| = 64 \wedge \big((sig = body \wedge ht = 0) \vee (\exists b.\ sig = body \,\|\, [b] \wedge b = ht \ne 0)\big) \wedge \mathrm{sigHashSchnorr}(c.tx, spent, c.nIn, ht, \mathrm{tapscript}{=}\mathtt{false}, \langle \mathtt{false}, [], [], \mathtt{0xFFFFFFFF}\rangle) = \mathrm{some}\ h \wedge \mathrm{schnorrVerify}(q, h, body) = \mathtt{true}.$$
--   A key-path spend verifies exactly when the witness is a BIP340 signature by the output key of the BIP341 signature hash: 64 bytes under `SIGHASH_DEFAULT`, or 65 bytes under the non-zero hash type of the last byte.
--
--   **Formalization Note.** `taprootHandler` is the version-1 branch of `VerifyWitnessProgram` as plugged into the published `VerifyScript`; the equivalence holds for every flag set, transaction and amount. The script path is covered by `scriptpath_commitment`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSig
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.keypath_correct (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr c.tx spent c.nIn ht false ⟨false, [], [], 0xFFFFFFFF⟩ = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by sorry
