-- Prove2me | Theorems.Thm_BlockBochner_lemma_13
-- name    : BlockBochner.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:08.348209+00:00
-- url     : https://prove2.me/theorems/b02605a7-9722-4f66-a4fe-80f3874caca2
-- title:
--   Lemma 13 — equivalent forms of link spectral gaps
-- statement:
--   Let $\nu$ be a connected, nontrivial codimension-$k$ link, $k\ge2$, i.e. a probability measure on a product of $k$ standard Borel spin spaces whose Glauber Laplacian has only constants in its kernel, with $L^2_0(\nu)\ne0$. For $0\le\gamma<1$ the following are equivalent:
--   1. $\lambda_2(L_{\mathrm{Glaub},\nu})\ge(1-\gamma)/k$, or equivalently $\lambda_2(P_{\mathrm{Glaub},\nu})\le1-(1-\gamma)/k$;
--   2. $c_\nu\le\dfrac{k-2+\gamma}{k-1}$;
--   3. $\sup\sigma(S_{\nu,0})\le\dfrac{k-2+\gamma}{k-1}$;
--   4. $\|P_\nu\Pi_{\Delta_\nu}\|^2_{\mathrm{op}}\le1-\dfrac{1-\gamma}k$;
--   5. $\|L_\nu(I-\Pi_{\Delta_\nu})-\Pi_{N_\nu}\|^2_{\mathrm{op}}\le1-\dfrac{1-\gamma}k$.
--
--   Here $\lambda_2(L_{\mathrm{Glaub},\nu})=\inf\sigma(L_{\mathrm{Glaub},\nu}|_{L^2_0(\nu)})$ and $\lambda_2(P_{\mathrm{Glaub},\nu})=\sup\sigma(P_{\mathrm{Glaub},\nu}|_{L^2_0(\nu)})$.
--
--   The lemma relates the spectral-gap hypothesis on two-site links to correlation and angle conditions.
--
--   **Formalization Note** The infimum and supremum of the spectrum of a self-adjoint operator are written as bounds on its quadratic form, over $L^2_0(\nu)$ or over $g$ with $g_i\in U^\nu_i$. The two forms of condition 1 are listed as separate equivalent conditions.
--
--   Differences from the source:
--   - encoding: ν = µ^τ a codimension-k link of a spin system → ν any probability measure on a product of k = card ι ≥ 2 standard Borel spaces; reason: every link is such a measure, and every such measure is a codimension-k link of itself with nothing pinned
--   - reading: "nontrivial" link → L²₀(ν) ≠ 0, i.e. ν is not a point mass; reason: the source does not define the word; this is the only reading under which the spectral quantities are defined
--   - encoding: inf σ(L_Glaub,ν|L²₀), sup σ(P_Glaub,ν|L²₀), sup σ(S_ν,0) → bounds on the quadratic forms over L²₀(ν), resp. over g with g_i ∈ U^ν_i; reason: for a self-adjoint operator the extremes of the spectrum are those of the numerical range
--   - encoding: condition 1 with its "or equivalently" clause → two entries of the TFAE list; reason: the clause is itself an equivalence
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Lemma 13, pp.17–18 (definitions pp.16–17)

import Mathlib
import Definitions.Def_BlockBochner_IsConnectedGlauber
import Definitions.Def_BlockBochner_genCorr
import Definitions.Def_BlockBochner_partialWalk
import Definitions.Def_BlockBochner_condExpDiag
import Definitions.Def_BlockBochner_diagAvg
import Definitions.Def_BlockBochner_Nspace
import Definitions.Def_BlockBochner_projCl

open MeasureTheory

namespace BlockBochner

/-- **Lemma 13 (equivalent forms of link spectral gaps).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Lemma 13, pp.17–18 (definitions
pp.16–17). Let `ν` be a connected, nontrivial codimension-`k` link, `k ≥ 2`. For `0 ≤ γ < 1` the
following are equivalent:
1. `λ₂(L_Glaub,ν) ≥ (1 − γ)/k`, or equivalently `λ₂(P_Glaub,ν) ≤ 1 − (1 − γ)/k`;
2. `c_ν ≤ (k − 2 + γ)/(k − 1)`;
3. `sup σ(S_{ν,0}) ≤ (k − 2 + γ)/(k − 1)`;
4. `‖P_ν Π_{∆ν}‖²_op ≤ 1 − (1 − γ)/k`;
5. `‖L_ν(I − Π_{∆ν}) − Π_{N_ν}‖²_op ≤ 1 − (1 − γ)/k`.

**Formalization Note** `ν` is any probability measure on a product of `k = card ι ≥ 2` standard Borel
spaces (each such measure is a codimension-`k` link with nothing pinned, and each link is such a
measure). "Nontrivial" is `L²₀(ν) ≠ 0`. `λ₂(L_Glaub,ν) = inf σ(L_Glaub,ν|L²₀(ν))` and
`λ₂(P_Glaub,ν) = sup σ(P_Glaub,ν|L²₀(ν))`, and `sup σ(S_{ν,0})`, are written as bounds on the
quadratic forms over `L²₀(ν)`, resp. `⊕_i U^ν_i` (for a self-adjoint operator the infimum and supremum
of the spectrum are those of the numerical range). The two forms of condition 1 are listed
separately. `P_ν`, `L_ν = I − P_ν`, `Π_{∆ν}` act on `⊕_{i} L²₀(ν)`. -/
theorem lemma_13 {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    [∀ i, StandardBorelSpace (X i)] (ν : Measure (∀ i, X i)) [IsProbabilityMeasure ν]
    (hk : 2 ≤ Fintype.card ι) (hconn : IsConnectedGlauber ν) (hnt : L20 ν ≠ ⊥)
    {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) :
    List.TFAE [
      ∀ f ∈ L20 ν, (1 - γ) / Fintype.card ι * ‖f‖ ^ 2 ≤ inner ℝ f (glauberLap ν f),
      ∀ f ∈ L20 ν, inner ℝ f (((Fintype.card ι : ℝ)⁻¹ • ∑ i, condExpOn ν {i}ᶜ) f) ≤
        (1 - (1 - γ) / Fintype.card ι) * ‖f‖ ^ 2,
      genCorr ν ≤ (Fintype.card ι - 2 + γ) / (Fintype.card ι - 1),
      ∀ g : PiLp 2 (fun _ : ι => Lp ℝ 2 ν), (∀ i, g i ∈ Uspace ν i) →
        inner ℝ g (partialWalk ν g) ≤ (Fintype.card ι - 2 + γ) / (Fintype.card ι - 1) * ‖g‖ ^ 2,
      ‖condExpDiag ν ∘L diagAvg ν‖ ^ 2 ≤ 1 - (1 - γ) / Fintype.card ι,
      ‖(1 - condExpDiag ν) ∘L (1 - diagAvg ν) - projCl (H := PiLp 2 (fun _ : ι => L20 ν)) (Nspace ν)‖ ^ 2 ≤
        1 - (1 - γ) / Fintype.card ι] := by sorry

end BlockBochner
