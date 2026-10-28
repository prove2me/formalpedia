-- Prove2me | Theorems.Thm_BitcoinTaproot_sighash_type_invalid
-- name    : BitcoinTaproot.sighash_type_invalid
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:36:18.360654+00:00
-- url     : https://prove2.me/theorems/9b9c58db-8af5-4c62-9da6-70016ab123d7
-- title:
--   Undefined hash types are rejected
-- statement:
--   For a hash type outside $\{0,1,2,3\} \cup \{0x81,0x82,0x83\}$, `sigHashSchnorr` is `none` (the signature check fails).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.sighash_type_invalid (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (h : ¬ (hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83))) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by sorry
