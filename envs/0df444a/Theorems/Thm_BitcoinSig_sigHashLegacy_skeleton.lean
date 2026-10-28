-- Prove2me | Theorems.Thm_BitcoinSig_sigHashLegacy_skeleton
-- name    : BitcoinSig.sigHashLegacy_skeleton
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:19:19.136987+00:00
-- url     : https://prove2.me/theorems/7d188518-0e21-40f9-9745-29c5b0b1492d
-- title:
--   The legacy sighash ignores scriptSigs and witnesses
-- statement:
--   For every script code, index and hash type, two transactions with the same version, outputs, lock time, and the same prevouts and sequence numbers in order have the same legacy signature hash. Signatures therefore never sign other signatures.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.sigHashLegacy_skeleton (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by sorry
