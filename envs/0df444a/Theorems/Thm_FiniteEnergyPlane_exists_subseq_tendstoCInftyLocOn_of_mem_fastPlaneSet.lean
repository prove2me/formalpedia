-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_mem_fastPlaneSet
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_of_mem_fastPlaneSet
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:06:08.055682+00:00
-- url     : https://prove2.me/theorems/9592efd7-cff6-441c-b9aa-9cb499115059
-- title:
--   Subsequential $C^\infty_{\mathrm{loc}}$ limits of normalized fast planes off a finite set
-- statement:
--   Let $P=(x,T)$ be a periodic Reeb orbit on a strictly star-shaped level $S\subset\mathbb{R}^4$, and $0<\gamma$ smaller than every period at most $T$. Every sequence $u_k$ in the set $\Theta(K,P)$ of fast finite-energy planes asymptotic to $P$ at $\infty$ with $u_k(0)\in K$ and $d\lambda$-energy $\gamma$ outside the closed unit disk has a subsequence and a finite set $\Gamma$ in the closed unit disk with the following properties. The planes shifted so that $a_k(2)=0$ converge in $C^\infty_{\mathrm{loc}}(\mathbb{C}\setminus\Gamma)$ to a finite-energy $\tilde J$-holomorphic curve $w$ on $\mathbb{C}\setminus\Gamma$ with $E(w)\le T$. The gradients of $u_k$ are uniformly bounded on compact subsets of $\mathbb{C}\setminus\Gamma$, and every point of $\Gamma$ is a limit of points at which the gradients tend to $\infty$.
--
--   This is the common starting point for describing limits of fast planes.
--
--   **Formalization Note** $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$ is `V 1 \ {0}`, with $a$ = `aCoord H` and $\mathrm{pr}$ = `proj H`; $\Theta$ = `fastPlaneSet H J P K γ`. The shift by $a_k(2)$ in $\mathbb{R}\times S$ is the radial scaling $e^{-2a_k(2)}\cdot$ in `V 1`. Convergence is `JHolomorphic.TendstoCInftyLocOn` on $(\uparrow\Gamma)^c$.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` be a periodic Reeb orbit on `S ⊂ ℝ⁴` and `0 < γ` smaller than every period at most `P.T`.
Every sequence `uₖ` in `fastPlaneSet H J P K γ` has a subsequence and a finite set `Γ` in the closed
unit disk such that the shifted planes `e^{-2aₖ(2)} • uₖ` (`aₖ = aCoord H ∘ uₖ`) converge in
`C^∞_loc(ℂ \ Γ)` to a finite-energy `J̃`-holomorphic curve `w` on `ℂ \ Γ` with `E(w) ≤ P.T`, the
gradients are bounded on compact subsets of `ℂ \ Γ`, and every point of `Γ` is a limit of points
where the gradients tend to `∞`. -/
theorem exists_subseq_tendstoCInftyLocOn_of_mem_fastPlaneSet (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (K : Set (V 1)) (γ : ℝ) (hγ : 0 < γ)
    (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (∀ z ∈ Γ, ‖z‖ ≤ 1) ∧ ∃ w : ℂ → V 1,
      IsFiniteEnergyCurve H J (↑Γ)ᶜ w ∧ energy H (↑Γ)ᶜ w ≤ ENNReal.ofReal P.T ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun k z => Real.exp (-(2 * aCoord H (u (φ k) 2))) • u (φ k) z) w (↑Γ)ᶜ ∧
      (∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc →
        ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, gradNorm H (u (φ k)) z ≤ M) ∧
      ∀ z ∈ Γ, ∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧
        Tendsto (fun k => gradNorm H (u (φ k)) (ζ k)) atTop atTop := by
  sorry

end FiniteEnergyPlane
