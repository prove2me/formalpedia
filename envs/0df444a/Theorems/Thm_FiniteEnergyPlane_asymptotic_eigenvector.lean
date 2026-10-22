-- Prove2me | Theorems.Thm_FiniteEnergyPlane_asymptotic_eigenvector
-- name    : FiniteEnergyPlane.asymptotic_eigenvector
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:44:31.876135+00:00
-- url     : https://prove2.me/theorems/8210ad9e-29ca-4579-a9cb-4abc3488f95e
-- title:
--   Asymptotic eigenvalue and eigenvector at a nondegenerate puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $D$ the open unit disk, and $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$. Suppose $0$ is a nondegenerate puncture of $u$ (Hryniewicz, Definition 2.9 (1), (2), (4)), asymptotic to a periodic Reeb orbit $P=(x,T)$ with sign $\varepsilon=\pm1$, in the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$; $P$ is not assumed nondegenerate. Then:
--   1. there is $b>0$ such that $u$ has exponential asymptotics with rate $b$: for some $d,c$, both $a(s,t)-\varepsilon Ts-d$ and $w(s,t)-x(\varepsilon Tt+c)$ decay like $e^{-bs}$ with all derivatives;
--   2. if $\pi\,du$ does not vanish identically on any punctured neighbourhood of $0$, there are an eigenvalue $\mu$ of $A_P$ with $\varepsilon\mu<0$ and an eigenvector $v$ for $\mu$ such that, for $s$ large,
--   $$w(s,t)=\mathrm{proj}\Big(x(\tau(s,t))+e^{\varepsilon\mu s}\big(v(\tau(s,t)/T)+r(s,t)\big)\Big),\qquad e^{\varepsilon\mu s}\big(v(\tau/T)+r\big)\in\xi_{x(\tau)},$$
--   with $\tau(s,t)-\varepsilon Tt-c\to0$ and $r\to0$ in $C^\infty$ as $s\to+\infty$.
--
--   **Formalization Note** The hypothesis is `IsNondegenerateEnd H u cylEnd P ε`; the conclusions are `HasExpAsymptoticsEnd` and `HasAsymptoticEigenvector` (defined in `FiniteEnergyPlane_Asymptotics`). "Not identically zero near $0$" is: every $B_r(0)\setminus\{0\}$, $r>0$, contains $z$ with `dlambdaDensity H u z ≠ 0`. Hryniewicz writes the leading term in a Martinet tube for $n=1$; here it is written in the tube $(\tau,h)\mapsto\mathrm{proj}(x(\tau)+h)$, $h\in\xi_{x(\tau)}$, in any dimension.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 and Lemma 2.12; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Corollary 6.6; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, with the Correction, ibid. 15 (1998), 535–538

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Theorem 2.11 and Lemma 2.12: let `u` be a finite-energy `J̃`-holomorphic curve on
`D \ {0}` whose puncture `0` is nondegenerate in the sense of Definition 2.9, asymptotic to a
periodic Reeb orbit `P` (not assumed nondegenerate) with sign `ε`. Then `u` converges to the
trivial cylinder over `P` exponentially fast in `C^∞`. If moreover `π du` does not vanish
identically near `0`, then `u` has an asymptotic eigenvalue `μ` with `εμ < 0` and an asymptotic
eigenvector `v` of `A_P` at the puncture. -/
theorem asymptotic_eigenvector {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u cylEnd P ε) :
    (∃ b > 0, HasExpAsymptoticsEnd H u cylEnd P ε b) ∧
      ((∀ r > 0, ∃ z ∈ ball (0 : ℂ) r \ {0}, dlambdaDensity H u z ≠ 0) →
        ∃ (μ : ℝ) (v : ℝ → V n), HasAsymptoticEigenvector H J u cylEnd P ε μ v) := by
  sorry

end FiniteEnergyPlane
