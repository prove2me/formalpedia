-- Prove2me | Theorems.Thm_BetheKS_lemma_A_3
-- name    : BetheKS.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:39.797056+00:00
-- url     : https://prove2.me/theorems/cea7514d-48a5-43ed-b809-517c2275bd16
-- title:
--   Lemma A.3 — existence, uniqueness and $L^1$-continuity of the root cavity weight $\Gamma_\delta$
-- statement:
--   Fix $t\ge\sqrt d>1$. For each $\delta>0$ there is a unique, up to $\nu$-almost-sure equality, measurable function $\Gamma_\delta:\Omega\to[0,c_\delta]$ satisfying (3.3),
--   $$
--   \Gamma(T)=\frac{t}{t^2+K+\delta-t\sum_{j=1}^K\Gamma(T_j)} .
--   $$
--   Moreover, $\delta\mapsto\Gamma_\delta$ is continuous in $L^1(\nu)$ on $(0,\infty)$.
--
--   Differences from the source:
--
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - reading: Γ_δ satisfying (3.3) → (3.3) holds ν-almost surely; uniqueness is among all measurable [0, c_δ]-valued a.e. solutions; reason: uniqueness is 'up to ν-almost-sure equality', and the paper's convention is that identities on Ω hold with probability 1 (p.7)
--   - encoding: δ ↦ Γ_δ continuous in L¹(ν) → for every family of solutions (Γ_δ)_{δ>0}, ∫|Γ_δ − Γ_{δ₀}| dν → 0 as δ → δ₀ within (0, ∞); reason: by uniqueness the family is determined up to null sets for each δ
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma A.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_BetheKS_cavityIter
import Definitions.Def_BetheKS_GWTree

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

/-- **Lemma A.3** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.13
(PDF p.14): fix `t ≥ √d > 1`. For each `δ > 0` there is a unique, up to `ν`-almost-sure equality,
measurable function `Γ_δ : Ω → [0, c_δ]` satisfying (3.3),
`Γ(T) = t / (t² + K + δ − t ∑_{j=1}^K Γ(T_j))`. Moreover, `δ ↦ Γ_δ` is continuous in `L¹(ν)` on
`(0, ∞)`.

**Formalization Note.** (3.3) is required `ν`-a.e. The continuity clause is stated for every family
`δ ↦ Γ_δ` of such solutions (by uniqueness, any two families agree a.e. for each `δ`). -/
theorem lemma_A_3 (d t : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) :
    (∀ δ : ℝ, 0 < δ → ∃ Γ : Offspring → ℝ,
      (Measurable Γ ∧ (∀ K, Γ K ∈ Set.Icc 0 (cDelta t δ)) ∧
        ∀ᵐ K ∂gwLaw d, Γ K = t / (t ^ 2 + (K [] : ℝ) + δ -
          t * ∑ j ∈ Finset.range (K []), Γ (subtree K j))) ∧
      ∀ Γ' : Offspring → ℝ,
        (Measurable Γ' ∧ (∀ K, Γ' K ∈ Set.Icc 0 (cDelta t δ)) ∧
          ∀ᵐ K ∂gwLaw d, Γ' K = t / (t ^ 2 + (K [] : ℝ) + δ -
            t * ∑ j ∈ Finset.range (K []), Γ' (subtree K j))) →
        Γ' =ᵐ[gwLaw d] Γ) ∧
    (∀ Γs : ℝ → Offspring → ℝ,
      (∀ δ : ℝ, 0 < δ → Measurable (Γs δ) ∧ (∀ K, Γs δ K ∈ Set.Icc 0 (cDelta t δ)) ∧
        ∀ᵐ K ∂gwLaw d, Γs δ K = t / (t ^ 2 + (K [] : ℝ) + δ -
          t * ∑ j ∈ Finset.range (K []), Γs δ (subtree K j))) →
      ∀ δ₀ : ℝ, 0 < δ₀ →
        Tendsto (fun δ => ∫ K, |Γs δ K - Γs δ₀ K| ∂gwLaw d) (𝓝[Set.Ioi 0] δ₀) (𝓝 0)) := by sorry

end BetheKS
