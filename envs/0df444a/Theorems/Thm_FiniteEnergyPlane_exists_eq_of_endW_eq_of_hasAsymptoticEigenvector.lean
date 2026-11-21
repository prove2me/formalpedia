-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eq_of_endW_eq_of_hasAsymptoticEigenvector
-- name    : FiniteEnergyPlane.exists_eq_of_endW_eq_of_hasAsymptoticEigenvector
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T21:11:14.877159+00:00
-- url     : https://prove2.me/theorems/b8247955-babb-48bf-ac2f-aec845bfb246
-- title:
--   Far-field injectivity along an end with an asymptotic eigenvector
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with compatible $J$ on $\xi$, $P=(x,T)$ a prime periodic Reeb orbit, and $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ asymptotic to $P$ at $\infty$ (`IsNondegenerateEnd H u cylInf P 1`) with an asymptotic eigenvalue $\mu$ and asymptotic eigenvector $v$ of $A_P$ there (`HasAsymptoticEigenvector H J u cylInf P 1 μ v`, Hryniewicz's Theorem 2.11). Write $w(s,t)=\mathrm{proj}(u(e^{2\pi(s+it)}))$. Then there is $S_0$ such that for all $s,s'\ge S_0$ and $t,t'\in\mathbb{R}$,
--   $$w(s,t)=w(s',t')\ \Longrightarrow\ e^{2\pi(s+it)}=e^{2\pi(s'+it')}.$$
--
--   Role: the $S$-component of $u$ is injective on a neighbourhood of $\infty$ (Hryniewicz (100), far-far case).
--
--   **Formalization Note** No holomorphicity of $u$ is assumed; only the asymptotic description at $\infty$ is used.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22 / (100); U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.11

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Injectivity far out along an end with an asymptotic eigenvector. Let `P` be a prime periodic
Reeb orbit and let `u` be asymptotic to `P` at `∞` (`IsNondegenerateEnd`), with an asymptotic
eigenvalue `μ` and eigenvector `v` there in the coordinates `cylInf` (Hryniewicz, Theorem 2.11).
Then for some `S`, the map `(s, t) ↦ w(s, t) = proj (u (e^{2π(s+it)}))` on `s ≥ S` takes equal
values only at the same point `e^{2π(s+it)}`. -/
theorem exists_eq_of_endW_eq_of_hasAsymptoticEigenvector {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (u : ℂ → V n)
    (huP : IsNondegenerateEnd H u cylInf P 1) (μ : ℝ) (v : ℝ → V n)
    (hv : HasAsymptoticEigenvector H J u cylInf P 1 μ v) :
    ∃ S : ℝ, ∀ s s' t t' : ℝ, S ≤ s → S ≤ s' →
      endW H u cylInf (s, t) = endW H u cylInf (s', t') → cylInf s t = cylInf s' t' := by
  sorry

end FiniteEnergyPlane
