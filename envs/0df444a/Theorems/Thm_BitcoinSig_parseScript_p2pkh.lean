-- Prove2me | Theorems.Thm_BitcoinSig_parseScript_p2pkh
-- name    : BitcoinSig.parseScript_p2pkh
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:21:12.80282+00:00
-- url     : https://prove2.me/theorems/7cebbdbe-bd26-4304-8ee4-7e1d4360b4e5
-- title:
--   The P2PKH bytes parse to the interpreter's P2PKH script
-- statement:
--   For every 20-byte $h$: `parseScript (p2pkhBytes h) = some (p2pkhScript h)` — the byte-level `GetScriptOp` parse of `76 a9 14 <h> 88 ac` is the instruction list the Script mission's theorems are stated on.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinSig BitcoinSer

theorem BitcoinSig.parseScript_p2pkh (h : Bytes) (hh : h.length = 20) :
    BitcoinSig.parseScript (BitcoinSig.p2pkhBytes h) = some (BitcoinScript.p2pkhScript h) := by sorry
