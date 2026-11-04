-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_of_fastPlaneSet
-- name    : FiniteEnergyPlane.exists_subseq_tendsto_of_fastPlaneSet
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T16:25:49.102514+00:00
-- url     : https://prove2.me/theorems/7aa2a5e5-4934-44de-8f6a-b3f1d4d17a31
-- title:
--   Limits of sequences of fast planes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit such that every periodic Reeb orbit of period at most $T_P$ is nondegenerate with $\mu_{CZ}\ge3$, let $\gamma>0$ be smaller than every such period and than every difference of two distinct such periods, and let $K\subset\mathbb{R}^4\setminus\{0\}$ be compact. Let $(u_k)$ be a sequence in $\Theta(K,P)$ and write $a_k=a\circ u_k$. Then there are a subsequence $(u_{k_j})$, a finite set $\Gamma$ in the closed unit disk and a finite-energy $\tilde J$-holomorphic curve $w$ on $\mathbb{C}\setminus\Gamma$ with $0<E(w)\le T_P$ such that the shifted planes $e^{-2a_{k_j}(2)}u_{k_j}$ (the $\mathbb{R}$-coordinate shifted by $-a_{k_j}(2)$) converge to $w$ in $C^\infty_{loc}(\mathbb{C}\setminus\Gamma)$, and one of the following holds:
--   1. $\inf a_{k_j}\to-\infty$, $\#\Gamma=1$, $\pi\,dw\equiv0$, and $K$ meets the cylinder $\mathbb{R}\times x(\mathbb{R})$ over $P=(x,T_P)$;
--   2. $\inf a_{k_j}\to A\in\mathbb{R}$, $\Gamma=\emptyset$, $a_{k_j}(2)\to c\in\mathbb{R}$, and $u_{k_j}\to e^{2c}w$ in $C^\infty_{loc}(\mathbb{C})$, where $e^{2c}w\in\Theta(K,P)$ and $a\circ(e^{2c}w)\ge A$.
--
--   **Formalization Note** Periods are those of `ReebOrbit H` (not necessarily minimal, so multiple covers count); $\mu_{CZ}\ge3$ is `Q.IsCZAtLeast 3`. "$\inf a_{k_j}\to-\infty$" is: for every $M$, eventually some $z$ has $a_{k_j}(z)\le M$. "$\inf a_{k_j}\to A$" is: for every $\varepsilon>0$, eventually $a_{k_j}\ge A-\varepsilon$ everywhere and $a_{k_j}(z)\le A+\varepsilon$ somewhere. "$\pi\,dw\equiv0$" is `piDs H w z = 0` for all $z\notin\Gamma$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 4.17

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 4.17. Let `P` be a periodic Reeb orbit on `S ⊂ ℝ⁴` such
that every periodic orbit of period at most `P.T` is nondegenerate with Conley–Zehnder index at
least `3`, let `0 < γ` be smaller than every such period and every difference of two distinct such
periods, and let `K ⊂ V 1 \ {0}` be compact. For every sequence `uₖ` in `fastPlaneSet H J P K γ`
there are a subsequence, a finite set `Γ` in the closed unit disk and a finite-energy
`J̃`-holomorphic curve `w` on `ℂ \ Γ` with `0 < E(w) ≤ P.T` such that the shifted planes
`e^{-2aₖ(2)} • uₖ` (`aₖ = aCoord H ∘ uₖ`) converge to `w` in `C^∞_loc(ℂ \ Γ)`, and one of the
following holds:
* `inf aₖ → -∞`, `Γ` has one point, `π dw ≡ 0`, and `K` meets the cone over the image of `P`;
* `inf aₖ → A ∈ ℝ`, `Γ = ∅`, `aₖ(2) → c`, and `uₖ → e^{2c} • w` in `C^∞_loc(ℂ)`, where
  `e^{2c} • w` belongs to `fastPlaneSet H J P K γ` and its coordinate `a` is at least `A`. -/
theorem exists_subseq_tendsto_of_fastPlaneSet (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H)
    (hP : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (hK : IsCompact K) (hK0 : (0 : V 1) ∉ K)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (∀ z ∈ Γ, ‖z‖ ≤ 1) ∧ ∃ w : ℂ → V 1,
      IsFiniteEnergyCurve H J (↑Γ)ᶜ w ∧ energy H (↑Γ)ᶜ w ≠ 0 ∧
      energy H (↑Γ)ᶜ w ≤ ENNReal.ofReal P.T ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun k z => Real.exp (-(2 * aCoord H (u (φ k) 2))) • u (φ k) z) w (↑Γ)ᶜ ∧
      (((∀ M : ℝ, ∀ᶠ k in atTop, ∃ z, aCoord H (u (φ k) z) ≤ M) ∧ Γ.card = 1 ∧
          (∀ z ∉ Γ, piDs H w z = 0) ∧ ∃ y ∈ K, proj H y ∈ Set.range P.x) ∨
        ∃ A : ℝ, (∀ ε > 0, ∀ᶠ k in atTop, ∀ z, A - ε ≤ aCoord H (u (φ k) z)) ∧
          (∀ ε > 0, ∀ᶠ k in atTop, ∃ z, aCoord H (u (φ k) z) ≤ A + ε) ∧ Γ = ∅ ∧
          ∃ c : ℝ, Tendsto (fun k => aCoord H (u (φ k) 2)) atTop (𝓝 c) ∧
            JHolomorphic.TendstoCInftyLocOn (fun k => u (φ k))
              (fun z => Real.exp (2 * c) • w z) Set.univ ∧
            (fun z => Real.exp (2 * c) • w z) ∈ fastPlaneSet H J P K γ ∧
            ∀ z, A ≤ aCoord H (Real.exp (2 * c) • w z)) := by
  sorry

end FiniteEnergyPlane
