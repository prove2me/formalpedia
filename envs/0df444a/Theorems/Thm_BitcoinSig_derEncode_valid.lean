-- Prove2me | Theorems.Thm_BitcoinSig_derEncode_valid
-- name    : BitcoinSig.derEncode_valid
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:21:24.879146+00:00
-- url     : https://prove2.me/theorems/7b2f6004-77e2-4f55-bb0e-a80057e849d6
-- title:
--   Strict DER accepts the canonical layout
-- statement:
--   For minimal big-endian integers $r, s$ (non-empty, top bit clear, no leading zero unless needed) with $|r| + |s| \le 66$ and any hash-type byte, `isValidSignatureEncoding (derEncode r s ht) = true`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.derEncode_valid (r s : Bytes) (ht : Byte) (hr : BitcoinSig.minimalInt r)
    (hs : BitcoinSig.minimalInt s) (hlen : r.length + s.length ≤ 66) :
    BitcoinSig.isValidSignatureEncoding (BitcoinSig.derEncode r s ht) = true := by sorry
