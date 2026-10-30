-- Prove2me | Theorems.Thm_BitcoinMuSig_partialSigAgg_schnorrVerify
-- name    : BitcoinMuSig.partialSigAgg_schnorrVerify
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:38:26.434623+00:00
-- url     : https://prove2.me/theorems/8e44b241-a2d9-45fd-8d23-945eff47cb41
-- title:
--   BIP327 end to end: partial signatures that verify aggregate to a BIP340 signature that verifies
-- statement:
--   For a session over a nonempty list of signers whose keys are the session's keys, whose nonces aggregate to the session's aggregate nonce, whose keys have order dividing $n$, and whose aggregate nonce point is not infinity: if every partial signature passes `partialSigVerifyInternal`, then the session values exist, `partialSigAgg` returns some `sig`, and the signature mission's `schnorrVerify (xbytes Q) msg sig = true`. All of BIP327's tweak accumulation, parity negations and encodings are included.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
import Definitions.Def_BitcoinSer
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.partialSigAgg_schnorrVerify (ctx : SessionCtx)
    (sigs : List (BitcoinSer.Bytes × BitcoinSer.Bytes × BitcoinSer.Bytes)) (hne : sigs ≠ [])
    (hpks : ctx.pks = sigs.map fun t => t.2.2) (hkeys : ∀ pk ∈ ctx.pks, n • tp (cpoint pk) = 0)
    (hagg : nonceAgg (sigs.map fun t => t.2.1) = some ctx.aggnonce)
    (hver : ∀ t ∈ sigs, partialSigVerifyInternal t.1 t.2.1 t.2.2 ctx = true)
    (hR : ∀ sv, getSessionValues ctx = some sv → sv.R' ≠ none) :
    ∃ sv sig, getSessionValues ctx = some sv ∧ partialSigAgg (sigs.map fun t => t.1) ctx = some sig ∧
      schnorrVerify (xbytes sv.Q) ctx.msg sig = true := by sorry
