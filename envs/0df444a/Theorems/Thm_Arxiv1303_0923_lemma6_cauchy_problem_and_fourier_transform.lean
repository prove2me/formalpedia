-- Prove2me | Theorems.Thm_Arxiv1303_0923_lemma6_cauchy_problem_and_fourier_transform
-- name    : Arxiv1303_0923.lemma6_cauchy_problem_and_fourier_transform
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:33:47.562933+00:00
-- url     : https://prove2.me/theorems/b4e47acc-6be4-405e-884e-58be6b70777c
-- title:
--   Lemma 6 (with $V_0$ corrected as in (70)): the Cauchy problem (68), (69), its decay, and the asymptotics (77), (83) of its time Fourier transform
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q$ satisfy (3), (4) with $m=4$ and let $g$ satisfy (13), (14). Then:
--
--   1. The Cauchy problem $V_{tt}=\Delta V-q(x)V$ in $\mathbb{R}^3\times(0,\infty)$, $V(x,0)=0$, $V_t(x,0)=g(x)$ has a solution $V$ with $V\in C^4(\overline\Phi\times[0,T])$ for every bounded domain $\Phi$ and every $T>0$, and it is unique on $\mathbb{R}^3\times[0,\infty)$: any two such solutions agree for all $t\ge0$.
--   2. For every bounded domain $\Phi$ there are $C_2,c_2>0$ depending on $q,g,\Phi$ with $|D^\beta_{x,t}V(x,t)|\le C_2e^{-c_2t}$ for $x\in\Phi$, $t\ge0$, $|\beta|\le4$ (eq. (75)), and for every $x\in\Phi$ the transform $v(x,k)=\int_0^\infty V(x,t)e^{ikt}\,dt$ is holomorphic in $k$ on $\{\operatorname{Im}k>-c_2\}$.
--   3. For every real $k$, $v(\cdot,k)$ is the unique solution in $C^5(\mathbb{R}^3)$ of (15)-(17) (eq. (76)).
--   4. Uniformly for $x\in\overline G$, as $|k|\to\infty$, $k\in\mathbb{C}_+$,
--   $$v(x,k)=\frac1{k^2}\Big[-g(x)+O\Big(\frac1k\Big)\Big],\qquad v_s(x,k)=\frac1{k^4}\big[-(qg)(x)+o(1)\big],$$
--   where $v_s=v-v_0$ (eqs. (77), (83)).
--
--   This is the analogue of Lemma 1 for the distributed source, and it is the analytic input of Theorems 3 and 4.
--
--   **Formalization Note** The paper defines $v_s=F(V-V_0)$ with $V_0$ given by (71); as printed, (71) lacks the factor $1/t$ of the Kirchhoff term in (70), and with that $V_0$ eq. (83) fails (the leading term would be of order $k^{-2}$). The intended $V_0$ is the solution for $q\equiv0$, whose transform is $v_0$; the statement uses $v_s=v-v_0$ directly, with $v_0$ given by its integral formula for complex $k$, consistent with the definition of $v_s$ in Theorem 4. The analytic continuation of $v(x,\cdot)$ is stated as holomorphy of the Fourier integral itself, which is the continuation the paper uses, and (77), (83) are stated for that integral. The bound (75) on all derivatives of order $\le4$ is written with the norm of the $j$-th derivative, $j\le4$, which is equivalent up to the constant $C_2$. $C^{5+\alpha}$ is weakened to $C^5$, in which the solution is still unique. In Lean $V$ is a function of all real $t$, and nothing constrains its values for $t<0$; uniqueness in item 1 is therefore stated, as in the paper, for $t\ge0$ only.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c011; Section 5.1, Lemma 6, eqs. (68)-(83), PDF pp. 14-16

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem lemma6_cauchy_problem_and_fourier_transform (geo : Geometry) (q g : R3 → ℝ)
    (hq : IsPotential geo.G 4 q) (hg : IsSourceTerm geo g) :
    (∃ V : R3 → ℝ → ℝ, IsCauchySolution q g V ∧
      ∀ W : R3 → ℝ → ℝ, IsCauchySolution q g W → ∀ x : R3, ∀ t : ℝ, 0 ≤ t → W x t = V x t) ∧
    ∀ V : R3 → ℝ → ℝ, IsCauchySolution q g V →
      (∀ Φ : Set R3, IsBoundedDomain Φ → ∃ C2 c2 : ℝ, 0 < C2 ∧ 0 < c2 ∧
        (∀ x ∈ Φ, ∀ t : ℝ, 0 ≤ t → ∀ j : ℕ, j ≤ 4 →
          ‖iteratedFDerivWithin ℝ j (fun p : R3 × ℝ => V p.1 p.2) (Set.univ ×ˢ Set.Ici 0)
            (x, t)‖ ≤ C2 * Real.exp (-c2 * t)) ∧
        ∀ x ∈ Φ, AnalyticOnNhd ℂ (timeFT V x) (shiftedHalfPlane c2)) ∧
      (∀ k : ℝ, IsSourceSolution q g k (fun x => timeFT V x k) ∧
        ∀ w : R3 → ℂ, IsSourceSolution q g k w → w = fun x => timeFT V x k) ∧
      (∃ C R : ℝ, ∀ x ∈ closure geo.G, ∀ k ∈ upperHalf, R ≤ ‖k‖ →
        ‖k ^ 2 * timeFT V x k + (g x : ℂ)‖ ≤ C / ‖k‖) ∧
      (∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ x ∈ closure geo.G, ∀ k ∈ upperHalf, R ≤ ‖k‖ →
        ‖k ^ 4 * (timeFT V x k - bgField geo.G g x k) + ((q x * g x : ℝ) : ℂ)‖ ≤ η) := by sorry

end Arxiv1303_0923
