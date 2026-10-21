-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_theorem_2_3
-- name    : CarbonFBSDE.MultiPeriod.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:43.113974+00:00
-- url     : https://prove2.me/theorems/dc521cd9-89ba-4897-9435-7b9dbff318db
-- title:
--   Theorem 2.3, p. 10 — the q-period carbon-market FBSDE has a unique solution with the compliance conditions (2.12) and a unique decoupling field
-- statement:
--   Let $q\ge1$, let $\Lambda_k\in\Theta$ for $1\le k\le q$, and consider the $q$-period model over $[T_0,T_1],\dots,[T_{q-1},T_q]$ with $T_0=0<T_1<\dots<T_q=T$, under Assumption 1, with interest rate $r\ge0$ and $\Lambda_k(\mathfrak e)-\mathfrak e\to+\infty$ as $\mathfrak e\to-\infty$. Then:
--
--   1. **Well-posedness.** For every period $k_0$, every start $t_0\in[T_{k_0-1},T_{k_0})$, every $(p,e)\in\mathbb R^d\times\mathbb R$ and every cap parameter $\mathfrak e$ for the period $k_0$, there is a unique (up to indistinguishability, and $Z$ up to $dt\otimes d\mathbb P$-null sets) tuple of a càdlàg $Y\in\mathcal S^{2,1}([t_0,T])$, continuous $E\in\mathcal S^{2,1}_c$, continuous $P\in\mathcal S^{2,d}_c$ and $Z\in\mathcal H^{2,d}$ with $(P,E)_{t_0}=(p,e)$, satisfying the dynamics (2.4) on each period and, almost surely for every $k$,
--   $$Y_{T_k-}=Y_{T_k}\ \text{if }E_{T_k}<\Lambda_k(E_{T_{k-1}}),\qquad Y_{T_k-}=1\ \text{if }E_{T_k}>\Lambda_k(E_{T_{k-1}}),\qquad Y_{T_k}\le Y_{T_k-}\le1\ \text{if }E_{T_k}=\Lambda_k(E_{T_{k-1}}),\tag{2.12}$$
--   with $Y_{T_q}=0$ (and $\mathfrak e$ in place of $E_{T_{k_0-1}}$ in the first period). The model of the paper is $k_0=1$, $t_0=0$, $\mathfrak e=e$.
--   2. **Continuity.** $Y$ is continuous on each period $[T_{k-1},T_k)$; it can jump at $T_k$.
--   3. **Decoupling field.** There is a function $v(t,p,e,\mathfrak e)$, continuous in $(t,p,e)$ on each $[T_{k-1},T_k)\times\mathbb R^d\times\mathbb R$ for every $\mathfrak e$, with $v(T,\cdot,\cdot,\cdot)=0$, such that every solution above satisfies $Y_t=v(t,P_t,E_t,E_{T_{k-1}})$ for $T_{k-1}\le t<T_k$.
--   4. **Uniqueness of $v$.** Any two such functions agree on $[0,T]\times\mathbb R^d\times\mathbb R\times\mathbb R$.
--
--   This is the paper's first main result: the allowance price of a multi-period emissions market with emission-dependent caps is well defined and is a deterministic function of the current factors, cumulative emissions, and emissions at the start of the period.
--
--   **Formalization Note** Three readings are labelled. (i) **Restarts (corrected).** As printed, "there exists a unique $v$ with $Y_t=v(t,P_t,E_t,E_{T_{k-1}})$" for a single start cannot be unique (with $b=\sigma=0$, only a curve of $(p,e)$ values is visited). Following Proposition 3.15 (5) and the proof on p. 27 ("for any $t_0,T'$…"), existence, uniqueness and the representation are posed for every restart $(k_0,t_0,p,e,\mathfrak e)$; this pins $v$ on $[0,T)$, and $v(T)=0$ by convention, so uniqueness is on $[0,T]$ only. The theorem names no initial values; $P_0=p$ is deterministic (p. 7). (ii) **Added hypotheses.** $r\ge0$ and $\Lambda_k(\mathfrak e)-\mathfrak e\to+\infty$ as $\mathfrak e\to-\infty$ are not on the page; the proof needs both (Corollary 3.14, and $\theta=\mathbf 1_{e\ge\Lambda_q(\mathfrak e)}\in\widehat{\mathcal K}$). (iii) "Y continuous on $[T_{k-1},T_k)$" is a conclusion, not part of the uniqueness class.
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, p. 10, Theorem 2.3, (2.12); restart reading from p. 26, Proposition 3.15 (5) and p. 27, proof of Theorem 2.3

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

theorem theorem_2_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : Basis d Ω)
    (hB : B.Valid) (c : Coeffs d) (L l1 l2 : ℝ) (hA : Assumption1 c L l1 l2) (r : ℝ)
    (hr : 0 ≤ r) (q : ℕ) (hq : 1 ≤ q) (Tg : ℕ → ℝ≥0) (hT0 : Tg 0 = 0)
    (hTg : ∀ k < q, Tg k < Tg (k + 1)) (Λ : ℕ → ℝ → ℝ)
    (hΛ : ∀ k, 1 ≤ k → k ≤ q → InTheta (Λ k))
    (hΛu : ∀ k, 1 ≤ k → k ≤ q → CapUnbounded (Λ k)) :
    -- (a) existence and uniqueness of (P, E, Y, Z) from every restart (k0, t0, p, e, 𝔢);
    --     the model of the page is k0 = 1, t0 = 0, 𝔢 = e
    (∀ k0, 1 ≤ k0 → k0 ≤ q → ∀ t0 ∈ Ico (Tg (k0 - 1)) (Tg k0), ∀ (p : SDEState d) (e ee : ℝ),
      (∃ P E Y Z, IsMultiSol B c r q Tg Λ k0 t0 p e ee P E Y Z) ∧
      (∀ P E Y Z P' E' Y' Z', IsMultiSol B c r q Tg Λ k0 t0 p e ee P E Y Z →
        IsMultiSol B c r q Tg Λ k0 t0 p e ee P' E' Y' Z' →
        SolAgree B (Icc t0 (Tg q)) (Icc t0 (Tg q)) t0 (Tg q) P E Y Z P' E' Y' Z')) ∧
    -- (b) Y is continuous on each period
    (∀ k0, 1 ≤ k0 → k0 ≤ q → ∀ t0 ∈ Ico (Tg (k0 - 1)) (Tg k0), ∀ (p : SDEState d) (e ee : ℝ)
      P E Y Z, IsMultiSol B c r q Tg Λ k0 t0 p e ee P E Y Z → ∀ k, k0 ≤ k → k ≤ q →
        ∀ᵐ ω ∂B.Pr, ContinuousOn (fun t => Y t ω) (Ico (max t0 (Tg (k - 1))) (Tg k))) ∧
    -- (c) a decoupling field exists
    (∃ v : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ, IsDecField B c r q Tg Λ v) ∧
    -- (d) and it is unique on [0, T]
    (∀ v v' : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ, IsDecField B c r q Tg Λ v →
      IsDecField B c r q Tg Λ v' → ∀ t ≤ Tg q, ∀ p e ee, v t p e ee = v' t p e ee) := by sorry

end CarbonFBSDE.MultiPeriod
