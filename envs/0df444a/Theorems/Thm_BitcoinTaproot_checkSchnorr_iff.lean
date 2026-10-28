-- Prove2me | Theorems.Thm_BitcoinTaproot_checkSchnorr_iff
-- name    : BitcoinTaproot.checkSchnorr_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:37:08.985053+00:00
-- url     : https://prove2.me/theorems/e553831a-fabe-4666-911e-5561a2ee6bfc
-- title:
--   CheckSchnorrSignature characterized
-- statement:
--   `checkSchnorrSignature tx spent nIn sig q tapscript ed = true` iff there are a 64-byte body, a hash type $ht$ and a message $h$ with: `sig` is the body and $ht = 0$, or `sig` is the body followed by one byte equal to $ht \ne 0$; `sigHashSchnorr … ht … = some h`; and `schnorrVerify q h body = true`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinSig
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.checkSchnorr_iff (tx : Tx) (spent : List TxOut) (nIn : Nat) (sig q : Bytes) (tapscript : Bool) (ed : ExecData) :
    BitcoinTaproot.checkSchnorrSignature tx spent nIn sig q tapscript ed = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr tx spent nIn ht tapscript ed = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by sorry
