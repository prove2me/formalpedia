-- Prove2me | Theorems.Thm_Arxiv1303_0923_lemma1_continuation_and_asymptotics
-- name    : Arxiv1303_0923.lemma1_continuation_and_asymptotics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:29:31.623777+00:00
-- url     : https://prove2.me/theorems/587716bf-3470-4f4f-b006-3e5a89624106
-- title:
--   Lemma 1 (frequency-domain part, with corrected constant in (35)): analytic continuation in $k$ and high-frequency asymptotics (34), (35)
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q$ satisfy (3), (4) with $m=2$, and for every source $x_0\in\mathbb{R}^3$ and every real $k$ let $u(\cdot,x_0,k)$ be the solution of (5)-(7) of the form (8), (9). Then:
--
--   1. For every $x_0\in\mathbb{R}^3$ and $k\in\mathbb{R}$ the problem (5)-(7) has exactly one solution of the form (8), (9).
--   2. For every $x_0\in\mathbb{R}^3$, every bounded domain $\Phi$ and every $\omega\in(0,1)$ there is $c_1=c_1(q,\Phi,x_0,\omega)>0$ such that for every $x\in\Phi\cap P_\omega(x_0)$ the function $k\mapsto u(x,x_0,k)$ admits an analytic continuation from $\mathbb{R}$ to $\{\operatorname{Im}k>-c_1\}$.
--   3. If $G\cap P_\omega(x_0)\neq\varnothing$ for some $\omega\in(0,1)$, and $u(x,x_0,\cdot)$ denotes this continuation, then uniformly for $x\in\overline G\cap P_\omega(x_0)$, as $|k|\to\infty$, $k\in\mathbb{C}_+$,
--   $$u(x,x_0,k)=\frac{e^{ik|x-x_0|}}{4\pi|x-x_0|}\Big[1+O\Big(\frac1k\Big)\Big],\qquad u_s(x,x_0,k)=-\frac{i\,e^{ik|x-x_0|}}{8\pi|x-x_0|\,k}\Big[\int_{L(x,x_0)}q(\xi)\,ds+O\Big(\frac1k\Big)\Big].$$
--
--   This is the analytic input of every uniqueness proof of the paper: it gives the half-plane of analyticity and the leading behaviour that Lemmas 2 and 3 and eq. (62) rest on.
--
--   **Formalization Note** Only the frequency-domain part of Lemma 1 is stated; the representation (23)-(32) of the time-domain solution $U$ of (21), (22) and the identity (33) $u=F(U)$ involve the distribution $\delta(t-|x-x_0|)$ and are not included. The paper's (35) has $16\pi$ in the denominator; the correct constant is $8\pi$ (see the mission report), and the statement uses $8\pi$. The asymptotics are written as $|u/u_0-1|\le C/|k|$ and $|2ik\,u_s/u_0-\int_Lq\,ds|\le C/|k|$ for $k\in\mathbb{C}_+$, $|k|\ge R$, uniformly in $x$; they are stated for every family of continuations analytic in a common half-plane $\{\operatorname{Im}k>-\gamma\}$, which by uniqueness of analytic continuation is the continuation of item 2. The uniform constant $c_1$ of item 2 is asserted for all $\omega\in(0,1)$; the paper's restriction $\omega<\omega_0(x_0,\Phi)$ only ensures $\Phi\cap P_\omega(x_0)\neq\varnothing$, and otherwise the statement is empty.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c006; Section 3.1, Lemma 1, eqs. (8), (9), (32)-(35), PDF pp. 7-8 (parts on the time-domain solution U, eqs. (23)-(31) and (33), not included)

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem lemma1_continuation_and_asymptotics (geo : Geometry) (q : R3 → ℝ)
    (hq : IsPotential geo.G 2 q) (u : R3 → R3 → ℝ → ℂ)
    (hu : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q x0 k (fun x => u x x0 k)) :
    (∀ (x0 : R3) (k : ℝ), ∃! w : R3 → ℂ, IsPointSourceSolution 2 q x0 k w) ∧
    (∀ (x0 : R3) (Φ : Set R3), IsBoundedDomain Φ → ∀ om ∈ Set.Ioo (0 : ℝ) 1,
      ∃ c1 : ℝ, 0 < c1 ∧ ∀ x ∈ Φ ∩ Pset om x0, ∃ F : ℂ → ℂ, IsContinuation c1 (u x x0) F) ∧
    (∀ (x0 : R3), ∀ om ∈ Set.Ioo (0 : ℝ) 1, (geo.G ∩ Pset om x0).Nonempty →
      ∀ (γ : ℝ), 0 < γ → ∀ F : R3 → ℂ → ℂ,
        (∀ x ∈ closure geo.G ∩ Pset om x0, IsContinuation γ (u x x0) (F x)) →
        (∃ C R : ℝ, ∀ x ∈ closure geo.G ∩ Pset om x0, ∀ k ∈ upperHalf, R ≤ ‖k‖ →
            ‖F x k / incWave x x0 k - 1‖ ≤ C / ‖k‖) ∧
        (∃ C R : ℝ, ∀ x ∈ closure geo.G ∩ Pset om x0, ∀ k ∈ upperHalf, R ≤ ‖k‖ →
            ‖2 * Complex.I * k * ((F x k - incWave x x0 k) / incWave x x0 k) -
              (segInt q x x0 : ℂ)‖ ≤ C / ‖k‖)) := by sorry

end Arxiv1303_0923
