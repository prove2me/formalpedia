-- Prove2me | Theorems.Thm_ColumnRandLP_dual_optimal_basic
-- name    : ColumnRandLP.dual_optimal_basic
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:47.997349+00:00
-- url     : https://prove2.me/theorems/cc672aad-5c87-4e4b-af20-fc960b7b61ca
-- title:
--   Proof of Theorem 1 — if $P_J$ is feasible and $\operatorname{rank}(A_J)=m$, $D_J$ has an optimal basic feasible solution, which is a basic solution of $D$
-- statement:
--   Let $A$ be an $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and suppose the complete problem $P:\min\{c^Tx\mid Ax=b,\ x\ge0\}$ is bounded. Let $J=(j_1,\dots,j_K)$ be a sample (repeated indices allowed) such that $P_J:\min\{c_J^T\tilde x\mid A_J\tilde x=b,\ \tilde x\ge0\}$ is feasible and $\operatorname{rank}(A_J)=m$. Then the dual $D_J:\max\{p^Tb\mid p^TA_J\le c_J^T\}$ has an optimal solution $p$ that is a basic feasible solution of $D_J$: there are $m$ distinct sampled indices $\beta_1,\dots,\beta_m\in\{j_1,\dots,j_K\}$ whose columns $A_{\beta_1},\dots,A_{\beta_m}$ are linearly independent and
--   $$
--   p^TA_{\beta_k}=c_{\beta_k}\qquad(k=1,\dots,m).
--   $$
--   In particular $p$ is a basic (not necessarily feasible) solution of the complete dual $D$.
--
--   In the proof of Theorem 1 this is what allows replacing $\|p\|_\infty$ in Proposition EC.3 by the bound $\gamma$ on all basic solutions of $D$.
--
--   **Formalization Note** The basis is an injective `β : Fin m → Fin n` with every `β k` in the range of `J`. "$P$ bounded" is that $c^Tx$ is bounded below on $F(P)$; the feasible solutions of $P_J$ embed in $F(P)$, so $P_J$ is bounded too.
--
--   Differences from the source:
--   - generalization: the standing assumptions of §3.1 (‖c‖₂ = 1, P feasible, rank(A) = m) → only P bounded below is assumed; reason: P feasible follows from P_J feasible, and the other two are not used; the statement specializes to the paper's setting
--   - encoding: an optimal basic feasible solution of D_J → IsDualOptimal for (A_J, b, c_J) and an injective β : Fin m → Fin n with range in J, linearly independent columns A_{β k} and pᵀA_{β k} = c_{β k}; reason: a basis of D_J is m sampled columns that are linearly independent (hence at distinct indices), and these equations are pᵀ = c_BᵀA_B⁻¹
--   - generalization: a sample of K ≥ 1 indices → any K, J : Fin K → Fin n (ordered, repeats allowed); reason: at K = 0 the hypothesis rank(A_J) = m forces m = 0; the statement specializes to the paper's K ≥ 1
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, proof of Theorem 1, p.ec9; basic dual solution §3.1, p.6

import Mathlib
import Definitions.Def_ColumnRandLP_StandardLP
import Definitions.Def_ColumnRandLP_Model

open Matrix

namespace ColumnRandLP

/-- **Proof of Theorem 1: an optimal basic dual solution** (Akchen–Mišić, arXiv:2007.10461v5,
proof of Theorem 1, p.ec9). If `P_J` is feasible and `rank(A_J) = m` (and `P` is bounded), then
the dual `D_J : max {pᵀb | pᵀA_J ≤ c_Jᵀ}` has an optimal basic feasible solution `p`; such a `p`
is a basic (not necessarily feasible) solution of the complete dual `D`.

**Formalization Note** Deterministic, for one sample `J : Fin K → Fin n` (repeats allowed). The
conclusion gives `p` optimal for `D_J` together with a basis of `D_J`: an injective
`β : Fin m → Fin n` whose values are sampled indices (`β k ∈ range J`), whose columns `A_{β k}`
are linearly independent, and with `pᵀA_{β k} = c_{β k}` for all `k`. This is the paper's
"basic feasible solution of `D_J`" and in particular `IsBasicDualSolution A c p`. "P bounded" is
`IsBoundedBelow A b c` (the objective is bounded below on `F(P)`); it makes `P_J` bounded, since
the feasible solutions of `P_J` embed in `F(P)`. -/
theorem dual_optimal_basic {m n K : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hPbdd : IsBoundedBelow A b c) (J : Fin K → Fin n)
    (hJ : IsFeasible (sampleMat A J) b) (hrank : (sampleMat A J).rank = m) :
    ∃ p : Fin m → ℝ, IsDualOptimal (sampleMat A J) b (sampleCost c J) p ∧
      ∃ β : Fin m → Fin n, Function.Injective β ∧ (∀ k, β k ∈ Set.range J) ∧
        LinearIndependent ℝ (fun k : Fin m => fun i : Fin m => A i (β k)) ∧
        ∀ k, (p ᵥ* A) (β k) = c (β k) := by sorry

end ColumnRandLP
