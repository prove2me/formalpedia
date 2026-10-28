-- Prove2me | Theorems.Thm_BitcoinSig_sigHashLegacy_anyoneCanPay
-- name    : BitcoinSig.sigHashLegacy_anyoneCanPay
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:19:32.883563+00:00
-- url     : https://prove2.me/theorems/8fbe1aa0-1016-4ea6-accd-5cf91980e1fb
-- title:
--   ANYONECANPAY signs only the signed input
-- statement:
--   With the `SIGHASH_ANYONECANPAY` bit set, the legacy hash of two transactions that agree on version, outputs, lock time and on the prevout and sequence of the signed input is the same, whatever their other inputs.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.sigHashLegacy_anyoneCanPay (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (hacp : hashType &&& BitcoinSig.SIGHASH_ANYONECANPAY ≠ 0)
    (h1 : tx'.version = tx.version) (h2 : tx'.vout = tx.vout) (h3 : tx'.nLockTime = tx.nLockTime)
    (h4 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout)
    (h5 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence) :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by sorry
