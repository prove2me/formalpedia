-- Prove2me | Theorems.Thm_BitcoinSig_derEncode_complete
-- name    : BitcoinSig.derEncode_complete
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:21:36.059297+00:00
-- url     : https://prove2.me/theorems/a1800f03-1b66-4d74-80d0-8a4ccbe005a4
-- title:
--   Strict DER accepts only the canonical layout
-- statement:
--   Every signature `IsValidSignatureEncoding` accepts is `derEncode r s ht` for minimal $r, s$ with $|r| + |s| \le 66$. Together with soundness this characterizes BIP66's strict encoding: exactly the sequences `30 L 02 |r| r 02 |s| s ht` with minimal positive integers and at most 73 bytes.
--
--   **Formalization Note.** The characterization is the goal because it is what every later layer consumes: the DERSIG rule is "the signature has this shape", and with it the lax parser and the strict test agree on their accepted values.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.derEncode_complete (sig : Bytes) (h : BitcoinSig.isValidSignatureEncoding sig = true) :
    ∃ (r s : Bytes) (ht : Byte), sig = BitcoinSig.derEncode r s ht ∧ BitcoinSig.minimalInt r ∧
      BitcoinSig.minimalInt s ∧ r.length + s.length ≤ 66 := by sorry
