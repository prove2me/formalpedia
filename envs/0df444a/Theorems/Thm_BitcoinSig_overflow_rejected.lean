-- Prove2me | Theorems.Thm_BitcoinSig_overflow_rejected
-- name    : BitcoinSig.overflow_rejected
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:20:17.75472+00:00
-- url     : https://prove2.me/theorems/d76640ea-b245-4a27-876e-f60190b75441
-- title:
--   An overflowed lax parse never verifies
-- statement:
--   If `parseDerLax sig = some (0, 0)` — the zero signature that the lax parser substitutes on overflow — then `pubkeyVerify pk hash sig = false` for every key and hash.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.overflow_rejected (pk hash sig : Bytes) (h : BitcoinSig.parseDerLax sig = some (0, 0)) :
    BitcoinSig.pubkeyVerify pk hash sig = false := by sorry
