-- Prove2me | Theorems.Thm_BNCovPack_SetCover_theorem_3_2
-- name    : BNCovPack.SetCover.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:19:12.083749+00:00
-- url     : https://prove2.me/theorems/d7df3792-7086-4e2b-9d94-2959f9445860
-- title:
--   Theorem 3.2 (covering half, set cover) — the $\{0,1\}$ scheme is $2\ln(1+\ell)$-competitive for fractional covering
-- statement:
--   Let $X$ be a finite set of elements and $\mathcal S$ a finite family of sets with positive costs $c(s)$, and for an element $e$ let $\mathcal S_e$ be the sets containing $e$. Elements arrive in a list $\sigma$; suppose every arriving element lies in at least one set and in at most $\ell$ sets, $1\le|\mathcal S_e|\le\ell$, with $\ell\ge 1$. Let $B>0$ and let $w$ be the weights produced by the Section 3 fractional scheme with $\{0,1\}$ coefficients and $n$ replaced by $\ell$ after processing $\sigma$. Then:
--
--   1. $w$ is a fractional cover of the arrived elements: $\sum_{s\in\mathcal S_e}w(s)\ge 1$ for every $e\in\sigma$;
--   2. for every fractional cover $w''\ge 0$ of the arrived elements ($\sum_{s\in\mathcal S_e}w''(s)\ge1$ for every $e\in\sigma$),
--   $$\sum_{s\in\mathcal S}c(s)\,w(s)\ \le\ 2\ln(1+\ell)\sum_{s\in\mathcal S}c(s)\,w''(s).$$
--
--   This is the covering half of Theorem 3.2 of the paper, in the set-cover form used in Section 5.1: the fractional algorithm is $O(\log\ell)$-competitive whatever the value of $B$. In Section 5.1 it supplies the bound $\sum_s w(s)\le 2\ln(1+d)\,OPT$ that turns the potential-function argument into the $O(\log d\log(n/OPT))$ guarantee.
--
--   **Formalization Note** The paper writes $O(\log\ell)$; the proof of Theorem 3.1, with $n$ replaced by $\ell$ and $a(i,j)\in\{0,1\}$, yields $2\ln(1+\ell)$ (claim (i) gives $X\le BY$, and claim (iii) with $x(s)\le 1$ makes $yB/(2\ln(1+\ell))$ dual feasible). The packing half of Theorem 3.2 (the dual solution does not violate the packing constraints) is not stated here. Logarithms are natural. The statement holds for every list $\sigma$, hence at every time of the run. The frequency bound is required only of arriving elements, as in the paper ("each primal constraint consists of at most $\ell$ non-zero coefficients").
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 5, Theorem 3.2 (covering half); explicit constant from the proof of Theorem 3.1, pp. 5-6, claims (i)-(iii), with n replaced by ℓ

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_BNCovPack_SetCover_FracScheme

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- **Theorem 3.2** (Buchbinder–Naor 2009, p. 5), covering half, on a set-cover instance
(`a ∈ {0,1}`): if every arriving constraint (element `e`) has at most `ℓ` non-zero coefficients
(`|𝒮_e| ≤ ℓ`), then for every `B > 0` the Section 3 scheme with `n` replaced by `ℓ`
(i) produces a feasible fractional cover of the arrived elements, and
(ii) has primal cost at most `2 ln(1 + ℓ)` times the cost of any fractional cover of them.
The paper writes `O(log ℓ)`; the proof of Theorem 3.1 with `n → ℓ` yields `2 ln(1 + ℓ)`. -/
theorem theorem_3_2 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (σ : List E) (hfreq : ∀ e ∈ σ, (inst.elemSets e).card ≤ ℓ)
    (hσ : ∀ e ∈ σ, (inst.elemSets e).Nonempty) :
    (∀ e ∈ σ, 1 ≤ elementWeight inst (fracRun inst B ℓ σ).w e) ∧
    ∀ w'' : T → ℝ, (∀ s, 0 ≤ w'' s) → (∀ e ∈ σ, 1 ≤ elementWeight inst w'' e) →
      ∑ s, inst.c s * (fracRun inst B ℓ σ).w s
        ≤ 2 * Real.log (1 + (ℓ : ℝ)) * ∑ s, inst.c s * w'' s := by sorry

end BNCovPack.SetCover
