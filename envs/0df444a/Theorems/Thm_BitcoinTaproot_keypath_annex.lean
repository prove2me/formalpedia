-- Prove2me | Theorems.Thm_BitcoinTaproot_keypath_annex
-- name    : BitcoinTaproot.keypath_annex
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:36:56.550593+00:00
-- url     : https://prove2.me/theorems/8b28742d-6bcb-4267-93f8-aee4d06708b9
-- title:
--   The key path commits to the annex
-- statement:
--   For a witness `[sig, annex]` with a non-empty annex starting with `0x50`, the Taproot handler equals the Schnorr check with execution data recording the annex and its hash $\mathrm{SHA256}(\mathrm{compactSize}(|annex|)\,\|\,annex)$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.keypath_annex (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig annex q : Bytes)
    (ha : (annex.getD 0 0).toNat = BitcoinTaproot.ANNEX_TAG) (hne : annex ≠ []) :
    BitcoinTaproot.taprootHandler spent c [sig, annex] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false
        ⟨true, BitcoinSer.sha256 (BitcoinSer.serBytes annex), [], 0xFFFFFFFF⟩ := by sorry
