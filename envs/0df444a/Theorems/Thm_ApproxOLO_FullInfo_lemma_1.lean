-- Prove2me | Theorems.Thm_ApproxOLO_FullInfo_lemma_1
-- name    : ApproxOLO.FullInfo.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:37.583991+00:00
-- url     : https://prove2.me/theorems/ba37466c-a0bc-40f9-a667-20a4591af19f
-- title:
--   Lemma 1, p. 6 — the extended approximation oracle: v · c ≤ min over αK, s dominates v on F, ‖v‖ ≤ (α + 2)R
-- statement:
--   Let $\mathcal K,\mathcal F\subset\mathbb R^d_+$, $R,F,C$ be an instance of online linear optimization (compact sets, $\mathcal K$ nonempty, $\|x\|\le R$ on $\mathcal K$, $\|f\|\le F$ on $\mathcal F$, $0\le x\cdot f\le C$), and let $\mathcal O_{\mathcal K}$ be an $\alpha$-approximation oracle for some $\alpha>0$. For every $c\in\mathbb R^d$, the extended oracle output $(v,s)=\hat{\mathcal O}_{\mathcal K}(c)$ of Eq. (2) satisfies $s\in\mathcal K$, $v\in\mathcal K+\mathcal B(0,(1+\alpha)R)$, and
--
--   1. $$v\cdot c\le\min_{x\in\alpha\mathcal K}x\cdot c;$$
--   2. for every $f\in\mathcal F$: $s\cdot f\le v\cdot f$ if $\alpha\ge1$, and $s\cdot f\ge v\cdot f$ if $\alpha<1$;
--   3. $\|v\|\le(\alpha+2)R$.
--
--   The extended oracle accepts every direction in $\mathbb R^d$, not only those in $\mathbb R^d_+$; it optimizes as well as any point of $\mathrm{CH}(\alpha\mathcal K)$ while returning, alongside the possibly infeasible point $v$, a feasible point $s$ that dominates it on every loss/payoff vector.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm. Membership in $\mathcal K+\mathcal B(0,(1+\alpha)R)$ is stated as $\|v-k\|\le(1+\alpha)R$ for some $k\in\mathcal K$ (closed ball), and item 1 as $v\cdot c\le(\alpha z)\cdot c$ for every $z\in\mathcal K$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, p. 6, Lemma 1 (Eq. (2))

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model

namespace ApproxOLO.FullInfo

open Matrix

/-- **Lemma 1 (Extended approximation oracle), Garber, arXiv:1709.03093v1, p. 6.** For every
`c ∈ ℝ^d`, `(v, s) = Ô_K(c)` satisfies `s ∈ K`, `v ∈ K + B(0, (1 + α)R)`, and
1. `v · c ≤ min_{x∈αK} x · c`;
2. `∀ f ∈ F`: `s · f ≤ v · f` if `α ≥ 1` and `s · f ≥ v · f` if `α < 1`;
3. `‖v‖ ≤ (α + 2)R`. -/
theorem lemma_1 {d : ℕ} (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha) (hO : IsApproxOracle K alpha O)
    (c : Vec d) :
    (extOracle O alpha R c).2 ∈ K ∧
    (∃ k ∈ K, euclNorm ((extOracle O alpha R c).1 - k) ≤ (1 + alpha) * R) ∧
    (∀ z ∈ K, (extOracle O alpha R c).1 ⬝ᵥ c ≤ (alpha • z) ⬝ᵥ c) ∧
    (∀ f ∈ Fs, (1 ≤ alpha → (extOracle O alpha R c).2 ⬝ᵥ f ≤ (extOracle O alpha R c).1 ⬝ᵥ f) ∧
      (alpha < 1 → (extOracle O alpha R c).1 ⬝ᵥ f ≤ (extOracle O alpha R c).2 ⬝ᵥ f)) ∧
    euclNorm (extOracle O alpha R c).1 ≤ (alpha + 2) * R := by sorry

end ApproxOLO.FullInfo
