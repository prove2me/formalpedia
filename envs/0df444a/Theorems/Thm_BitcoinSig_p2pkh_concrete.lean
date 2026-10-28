-- Prove2me | Theorems.Thm_BitcoinSig_p2pkh_concrete
-- name    : BitcoinSig.p2pkh_concrete
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T14:21:47.946714+00:00
-- url     : https://prove2.me/theorems/e08be808-49bc-4984-9029-6ba82d46a803
-- title:
--   P2PKH is correct against Core's concrete signature checker
-- statement:
--   For every flag setting, transaction, input index, amount and signature version, and every signature, key and hash within the 520-byte push limit:
--   $$\mathrm{verifyScriptPlain}\big(\mathrm{legacyOracle}(tx, nIn, \text{p2pkhBytes}(h)),\ [\langle sig\rangle, \langle pk\rangle],\ \mathtt{DUP\ HASH160}\ \langle h\rangle\ \mathtt{EQUALVERIFY\ CHECKSIG}\big) = \mathtt{true}$$
--   $$\iff \mathrm{Hash160}(pk) = h \;\wedge\; \mathrm{checkSigPreTapscript}(tx, nIn, \text{p2pkhBytes}(h), sig, pk) = \mathrm{some}\ \mathtt{true},$$
--   where the oracle is Core's RIPEMD-160∘SHA-256 and the pre-tapscript checker. Composed with `checkSig_base_iff`, the right-hand side is: valid encodings, a valid key, and ECDSA verification of the legacy sighash. This instantiates the Script mission's abstract P2PKH theorem with the concrete cryptography and sighash of the pinned source.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinSig BitcoinSer

theorem BitcoinSig.p2pkh_concrete (f : SigFlags) (fl : BitcoinScript.Flags) (tx : Tx) (nIn : Nat) (amount : Int)
    (v : SigVersion) (sig pk h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain fl (BitcoinSig.legacyOracle f tx nIn amount v (BitcoinSig.p2pkhBytes h))
        [.push sig, .push pk] (BitcoinScript.p2pkhScript h) = true ↔
      BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript f tx nIn amount v (BitcoinSig.p2pkhBytes h) sig pk = some true := by sorry
