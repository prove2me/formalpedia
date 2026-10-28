-- Prove2me | Theorems.Thm_BitcoinSig_checkSig_dersig
-- name    : BitcoinSig.checkSig_dersig
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:20:41.48631+00:00
-- url     : https://prove2.me/theorems/f2defd78-c52d-4a4c-af4d-cfc076cf7e9d
-- title:
--   With DERSIG a non-DER signature is a script error
-- statement:
--   If the `DERSIG` flag is set, a non-empty signature failing `IsValidSignatureEncoding` makes `checkSigPreTapscript` return `none` (the script fails), for every transaction, key and script code.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.checkSig_dersig (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode sig pk : Bytes) (hf : f.dersig = true) (hne : sig ≠ [])
    (hder : BitcoinSig.isValidSignatureEncoding sig = false) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode sig pk = none := by sorry
