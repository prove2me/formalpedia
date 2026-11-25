-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_rescaled_limit_of_tendsto_trivialCylinder
-- name    : FiniteEnergyPlane.exists_rescaled_limit_of_tendsto_trivialCylinder
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:39:34.737325+00:00
-- url     : https://prove2.me/theorems/baecead7-f768-5846-9f4f-cddf76b1f598
-- title:
--   Limits at the origin of disks converging to a trivial cylinder
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a prime periodic Reeb orbit, and suppose every periodic Reeb orbit of period at most $C$ is nondegenerate. Let $u_n$ be finite-energy $\tilde J$-holomorphic maps on the open unit disk $\mathring D$ with Hofer energy $E(u_n)\le C$, converging in $C^\infty_{loc}(\mathring D\setminus\{0\})$ to the trivial cylinder $F_P(e^{2\pi(s+it)})=(Ts,x(Tt))$. Then, for a subsequence, there are $z_n\to0$ in $\mathbb{C}$, $\delta_n\to0$ with $\delta_n>0$, $c_n\in\mathbb{R}$, a finite $\Gamma\subset\mathbb{C}$ and a finite-energy curve $v$ on $\mathbb{C}\setminus\Gamma$ with
--   $$(c_n\cdot u_{\varphi(n)})(z_n+\delta_nz)\to v\quad\text{in }C^\infty_{loc}(\mathbb{C}\setminus\Gamma),$$
--   such that
--
--   1. $v$ is asymptotic to $P$ at $\infty$, which is a positive puncture;
--   2. $\int v^*d\lambda>0$;
--   3. every point of $\Gamma$ is a negative puncture of $v$, asymptotic to a periodic Reeb orbit of period at most $C$.
--
--   Here $c\cdot u$ is the translate of $u$ by $c$ in the $\mathbb{R}$-direction. The boundary behaviour of $u_n$ plays no role, and $\Gamma$ may be empty.
--
--   **Formalization Note** $c\cdot u$ is `shiftA c u`, $z\mapsto e^{2c}u(z)$, and asymptotic is `IsNondegenerateEnd`. Periods are those of `ReebOrbit H`, not necessarily minimal, so multiple covers count.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 5.7; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, § 3.2, formula (34), and Lemma 3.8

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2012), Lemma 5.7; Hryniewicz (2014), § 3.2 (34) and Lemma 3.8. Let `P` be prime, and suppose every
periodic orbit of period at most `C` is nondegenerate. Let `u_n` be `J̃`-holomorphic maps on the open unit disk of
Hofer energy at most `C`, converging in `C^∞_loc` on the punctured disk to the trivial cylinder over `P`. After
passing to a subsequence there are `z_n → 0`, `δ_n → 0`, `δ_n > 0`, and `c_n ∈ ℝ` such that
`(c_n · u_n)(z_n + δ_n z)` converges in `C^∞_loc` on `ℂ \ Γ`, for a finite set `Γ`, to a finite-energy curve `v`
that is asymptotic to `P` at `∞`, has `∫ v*dλ > 0`, and whose punctures in `Γ` are negative and asymptotic
to orbits of period at most `C`. -/
theorem exists_rescaled_limit_of_tendsto_trivialCylinder (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (C : ℝ)
    (hnd : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate)
    (u : ℕ → ℂ → V 1) (hu : ∀ n, IsFiniteEnergyCurve H J (ball 0 1) (u n))
    (hE : ∀ n, energy H (ball 0 1) (u n) ≤ ENNReal.ofReal C)
    (hconv : JHolomorphic.TendstoCInftyLocOn u (trivialCylinder P) (ball 0 1 \ {0})) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (z : ℕ → ℂ) (δ c : ℕ → ℝ) (Γ : Finset ℂ) (v : ℂ → V 1),
      Tendsto z atTop (𝓝 0) ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ n, 0 < δ n) ∧
      JHolomorphic.TendstoCInftyLocOn (fun n w => shiftA (c n) (u (φ n)) (z n + δ n * w)) v
        (Γ : Set ℂ)ᶜ ∧
      IsFiniteEnergyCurve H J (Γ : Set ℂ)ᶜ v ∧ IsNondegenerateEnd H v cylInf P 1 ∧
      0 < dlambdaEnergy H (Γ : Set ℂ)ᶜ v ∧
      ∀ w ∈ Γ, ∃ Q : ReebOrbit H, Q.T ≤ C ∧ IsNondegenerateEnd H v (cylEndAt w) Q (-1) := by
  sorry

end FiniteEnergyPlane
