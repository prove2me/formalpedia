-- Prove2me | Theorems.Thm_BitcoinTaproot_sighash_single_missing
-- name    : BitcoinTaproot.sighash_single_missing
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:36:30.534226+00:00
-- url     : https://prove2.me/theorems/586c86a9-6c97-412c-8f28-ce02fce8585a
-- title:
--   SIGHASH_SINGLE without an output fails
-- statement:
--   For a valid hash type whose output type is `SIGHASH_SINGLE` and an input index with no corresponding output, `sigHashSchnorr` is `none`: unlike the legacy sighash there is no `uint256::ONE` quirk in BIP341.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.sighash_single_missing (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (hv : hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83)) (h3 : hashType &&& 3 = 3) (hout : tx.vout.length ≤ inPos) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by sorry
