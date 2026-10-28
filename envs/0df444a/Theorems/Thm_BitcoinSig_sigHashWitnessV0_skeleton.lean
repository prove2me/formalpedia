-- Prove2me | Theorems.Thm_BitcoinSig_sigHashWitnessV0_skeleton
-- name    : BitcoinSig.sigHashWitnessV0_skeleton
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:19:43.011977+00:00
-- url     : https://prove2.me/theorems/bc558d36-fc40-4815-bbb2-20f185bb0c06
-- title:
--   The BIP143 sighash ignores scriptSigs and witnesses
-- statement:
--   For every script code, index, hash type and amount, two transactions with the same skeleton have the same BIP143 signature hash.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.sigHashWitnessV0_skeleton (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat) (amount : Int)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashWitnessV0 scriptCode tx' nIn hashType amount =
      BitcoinSig.sigHashWitnessV0 scriptCode tx nIn hashType amount := by sorry
