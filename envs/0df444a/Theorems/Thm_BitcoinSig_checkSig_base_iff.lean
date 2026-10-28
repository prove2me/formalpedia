-- Prove2me | Theorems.Thm_BitcoinSig_checkSig_base_iff
-- name    : BitcoinSig.checkSig_base_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:20:57.594484+00:00
-- url     : https://prove2.me/theorems/bd4f0d81-d9d3-4f2b-95e9-c3f845befffb
-- title:
--   The legacy checker unfolded
-- statement:
--   `checkSigPreTapscript f tx nIn amount BASE scriptCode sig pk = some true` iff `CheckSignatureEncoding` and `CheckPubKeyEncoding` pass, the key is valid, and $sig = sig' ++ [ht]$ with `pubkeyVerify pk (sigHashLegacy (FindAndDelete scriptCode ⟨sig⟩) tx nIn ht) sig'`: the signature check is ECDSA verification of the legacy sighash of the signature-deleted script code, under the hash type given by the last byte.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.checkSig_base_iff (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int)
    (scriptCode sig pk : Bytes) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount .base scriptCode sig pk = some true ↔
      BitcoinSig.checkSignatureEncoding f sig = true ∧ BitcoinSig.checkPubKeyEncoding f .base pk = true ∧
      BitcoinSig.pubkeyValid pk = true ∧
      ∃ (sig' : Bytes) (ht : Byte), sig = sig' ++ [ht] ∧
        BitcoinSig.pubkeyVerify pk
          (BitcoinSig.sigHashLegacy (BitcoinSig.findAndDelete scriptCode (BitcoinSig.pushBytes sig)).1 tx nIn ht.toNat)
          sig' = true := by sorry
