-- Prove2me | Theorems.Thm_BlockBochner_lemma_13_two_sites
-- name    : BlockBochner.lemma_13_two_sites
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:11.63346+00:00
-- url     : https://prove2.me/theorems/6ba1979d-6023-4009-8b17-87d934df2fef
-- title:
--   Lemma 13, $k=2$ — $c_\nu=\rho_\nu(X_i,X_j)=\|P^\nu_iP^\nu_j-P^\nu_{ij}\|=\|L^\nu_iL^\nu_j-L^\nu_{ij}\|$
-- statement:
--   Let $\nu$ be a connected, nontrivial two-site link, $R=\{i,j\}$. Then
--   $$c_\nu=\rho_\nu(X_i,X_j)=\|P^\nu_iP^\nu_j-P^\nu_{ij}\|_{\mathrm{op}}=\|L^\nu_iL^\nu_j-L^\nu_{ij}\|_{\mathrm{op}},$$
--   where $\rho_\nu$ is the HGR maximal correlation (6), $P^\nu_{ij}$ and $L^\nu_{ij}$ are the orthogonal projections onto $\operatorname{ran}P^\nu_i\cap\operatorname{ran}P^\nu_j$ and $\operatorname{ran}L^\nu_i\cap\operatorname{ran}L^\nu_j$ in $L^2(\nu)$.
--
--   This identifies the two-site link condition with a maximal-correlation bound.
--
--   **Formalization Note** $\rho_\nu(X_i,X_j)$ is the published `CustomHedge.Exist.maximalCorrelation` of $\sigma(X_i)$ and $\sigma(X_j)$ under $\nu$: the supremum of the correlation of centred square-integrable functions of $X_i$ and $X_j$ with positive variances, $0$ if there are none. Taking the signed correlation is equivalent to $|\mathrm{Cov}|$ since $g$ may be replaced by $-g$.
--
--   Differences from the source:
--   - encoding: ν = µ^τ a two-site link → ν any probability measure on a product of two standard Borel spaces (card ι = 2); reason: every two-site link is such a measure and conversely
--   - reading: "nontrivial" link → L²₀(ν) ≠ 0; reason: as in Lemma 13
--   - encoding: ρ_ν(X_i, X_j) of (6), sup of |Cov(f(X_i), g(X_j))|/√(Var·Var) over f ∈ L²(ν_{X_i}), g ∈ L²(ν_{X_j}) with positive variances → CustomHedge.Exist.maximalCorrelation ν σ(X_i) σ(X_j), sup of the signed Pearson correlation over centred square-integrable σ(X_i)-, σ(X_j)-measurable functions with positive variances (0 if none); reason: the σ(X)-measurable functions are exactly the f(X); centring changes no correlation; |Cov| and the signed version have the same supremum (replace g by −g)
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Lemma 13, p.18 (k = 2 display); Eq. (6), p.16

import Mathlib
import Definitions.Def_BlockBochner_IsConnectedGlauber
import Definitions.Def_BlockBochner_genCorr
import Definitions.Def_BlockBochner_projCl
import Definitions.Def_CustomHedge_Exist_MaxCorr

open MeasureTheory

namespace BlockBochner

/-- **Lemma 13, the case `k = 2`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.2, p.18 (after Lemma 13): "when `k = 2` say
`R = {i, j}`, then we have the HGR maximal correlation in (6), and
`c_ν = ρ_ν(X_i, X_j) = ‖P^ν_i P^ν_j − P^ν_{ij}‖_op = ‖L^ν_i L^ν_j − L^ν_{ij}‖_op`."

Under the hypotheses of Lemma 13 (`ν` connected and nontrivial) with `k = 2`.

**Formalization Note** `ρ_ν(X_i, X_j)` of (6), p.16, is the published
`CustomHedge.Exist.maximalCorrelation` of the σ-algebras `σ(X_i)`, `σ(X_j)` under `ν` (supremum of the
correlation over centred square-integrable functions of `X_i`, resp. `X_j`, with positive variances;
`0` when there are none). `P^ν_{ij}`, `L^ν_{ij}` project onto `ran P^ν_i ∩ ran P^ν_j`, resp.
`ran L^ν_i ∩ ran L^ν_j`, in `L²(ν)`. -/
theorem lemma_13_two_sites {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, StandardBorelSpace (X i)] (ν : Measure (∀ i, X i))
    [IsProbabilityMeasure ν] (hk : Fintype.card ι = 2) {i j : ι} (hij : i ≠ j)
    (hconn : IsConnectedGlauber ν) (hnt : L20 ν ≠ ⊥) :
    genCorr ν = CustomHedge.Exist.maximalCorrelation ν (coordSigma {i}) (coordSigma {j}) ∧
    CustomHedge.Exist.maximalCorrelation ν (coordSigma {i}) (coordSigma {j}) =
      ‖condExpOn ν {i}ᶜ ∘L condExpOn ν {j}ᶜ -
        projCl (LinearMap.range (condExpOn ν {i}ᶜ).toLinearMap ⊓
          LinearMap.range (condExpOn ν {j}ᶜ).toLinearMap)‖ ∧
    ‖condExpOn ν {i}ᶜ ∘L condExpOn ν {j}ᶜ -
        projCl (LinearMap.range (condExpOn ν {i}ᶜ).toLinearMap ⊓
          LinearMap.range (condExpOn ν {j}ᶜ).toLinearMap)‖ =
      ‖siteLap ν i ∘L siteLap ν j - projCl (LinearMap.range (siteLap ν i).toLinearMap ⊓
        LinearMap.range (siteLap ν j).toLinearMap)‖ := by sorry

end BlockBochner
