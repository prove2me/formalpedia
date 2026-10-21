-- Prove2me | Theorems.Thm_EFXGenVal_TwoVal_theorem_1
-- name    : EFXGenVal.TwoVal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:01.142078+00:00
-- url     : https://prove2.me/theorems/5dd5e474-14e2-467e-9a4b-ff3d458eec1a
-- title:
--   Theorem 1, p. 3 — a complete EFX allocation exists when each agent has one of two general valuations
-- statement:
--   Let $n\ge 1$ agents share $m$ indivisible items. Each agent $i$ has a valuation $v_i:2^M\to\mathbb R$ that is normalized ($v_i(\emptyset)=0$) and monotone ($S\subseteq T\Rightarrow v_i(S)\le v_i(T)$), and nothing more is assumed (general valuations). Suppose there are two set functions $v_a,v_b$ such that every agent's valuation is one of them: $v_i\in\{v_a,v_b\}$ for all $i$. Then there exists a **complete EFX allocation**: a partition $X=(X_1,\dots,X_n)$ of all of $M$ into disjoint bundles such that no agent EFX envies another,
--   $$v_i(X_j\setminus\{g\})\le v_i(X_i)\qquad\text{for all agents } i,j \text{ and all } g\in X_j .$$
--
--   This extends the existence of complete EFX allocations from identical general valuations (Plaut–Roughgarden) and from two additive or nice cancelable valuations (Mahara; Berger et al.) to two arbitrary general valuations.
--
--   **Formalization Note** No additivity and no non-degeneracy are assumed. The only added hypothesis is $0<n$, and it is necessary: with no agents and at least one item there is no complete allocation. $v_a=v_b$ is allowed. Completeness is `pool X = ∅`, and EFX is the published `IsEFX`, which also ranges over $i=j$; that case holds automatically under monotonicity, so it agrees with the page's "no agent EFX envies another".
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, Theorem 1, p. 3

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

theorem theorem_1 {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v)
    (va vb : Finset (Fin m) → ℝ) (htype : ∀ i, v i = va ∨ v i = vb) :
    ∃ X : Fin n → Finset (Fin m), IsPartialAllocation X ∧ pool X = ∅ ∧ IsEFX v X := by sorry

end EFXGenVal.TwoVal
