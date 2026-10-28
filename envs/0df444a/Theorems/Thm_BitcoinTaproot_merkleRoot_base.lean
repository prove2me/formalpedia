-- Prove2me | Theorems.Thm_BitcoinTaproot_merkleRoot_base
-- name    : BitcoinTaproot.merkleRoot_base
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:34:37.152484+00:00
-- url     : https://prove2.me/theorems/75b4202c-ba90-4ed4-ad20-4a4f7dd6c13b
-- title:
--   An empty path commits to the leaf
-- statement:
--   For a 33-byte control block (no path nodes), `taprootMerkleRoot control leaf = leaf`: the merkle root of a single-leaf tree is the leaf hash itself.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.merkleRoot_base (control leaf : Bytes) (h : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot control leaf = leaf := by sorry
