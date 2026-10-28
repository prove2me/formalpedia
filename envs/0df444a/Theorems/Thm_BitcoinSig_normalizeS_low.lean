-- Prove2me | Theorems.Thm_BitcoinSig_normalizeS_low
-- name    : BitcoinSig.normalizeS_low
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:20:08.142168+00:00
-- url     : https://prove2.me/theorems/dfdf8b23-8afd-4b5a-9370-d06c5c67d626
-- title:
--   Normalization yields a low S
-- statement:
--   For every $s < n$, `isHighS (normalizeS s) = false`: after normalization $s \le n/2$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.normalizeS_low (s : Nat) (hs : s < BitcoinSig.n) :
    BitcoinSig.isHighS (BitcoinSig.normalizeS s) = false := by sorry
