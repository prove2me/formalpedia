-- Prove2me | Theorems.Thm_BitcoinMuSig_musig2_partialSigAgg
-- name    : BitcoinMuSig.musig2_partialSigAgg
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:36:31.273102+00:00
-- url     : https://prove2.me/theorems/aa8f8005-19a9-46df-b8a5-407b887d4f51
-- title:
--   MuSig2 partial-signature aggregation in any module
-- statement:
--   Over any commutative ring $K$ and $K$-module: if every partial signature satisfies $s_iG = \varepsilon(R_{1,i} + bR_{2,i}) + (e\,a_i\,g\,g_{acc})X_i$ and $Q = g_{acc}\sum a_iX_i + t_{acc}G$, then $(\sum s_i + e\,g\,t_{acc})G = \varepsilon(\sum R_{1,i} + b\sum R_{2,i}) + e(gQ)$: the BIP340 equation for the aggregate.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_partialSigAgg {ι K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (S : Finset ι) (G : M) (X R₁ R₂ : ι → M) (a s : ι → K) (b e g gacc tacc ε : K) (Q : M)
    (hQ : Q = gacc • ∑ i ∈ S, a i • X i + tacc • G)
    (hpart : ∀ i ∈ S, s i • G = ε • (R₁ i + b • R₂ i) + (e * a i * (g * gacc)) • X i) :
    (∑ i ∈ S, s i + e * g * tacc) • G = ε • (∑ i ∈ S, R₁ i + b • ∑ i ∈ S, R₂ i) + e • (g • Q) := by sorry
