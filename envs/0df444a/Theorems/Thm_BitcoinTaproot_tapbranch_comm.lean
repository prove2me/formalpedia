-- Prove2me | Theorems.Thm_BitcoinTaproot_tapbranch_comm
-- name    : BitcoinTaproot.tapbranch_comm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:34:26.150825+00:00
-- url     : https://prove2.me/theorems/c90a1dd0-8c2f-4dc7-996f-c11be4310ccb
-- title:
--   ComputeTapbranchHash is symmetric
-- statement:
--   For all byte strings $a, b$: `tapbranchHash a b = tapbranchHash b a`. The branch hash sorts its two children lexicographically, so the merkle path does not encode left/right.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.tapbranch_comm (a b : Bytes) : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash b a := by sorry
