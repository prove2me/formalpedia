-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff
-- name    : AlgebraicCurve.SemistableCovering.natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/f275d5fb-c78a-58ce-846c-8c5818ab5b92
-- title:
--   N-torsion bound for the Jacobian of a subdivided multigraph
-- statement:
--   Fix natural numbers $n$ and $m$, maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$ (a multigraph on $n$ vertices with $m$ oriented edges, loops and parallel edges allowed), and weights $W : \mathrm{Fin}\,m \to \mathbb{N}$ with $W_e > 0$ for all $e$. Assume connectivity in cut form: for every finite set $S$ of vertices with both $S$ and its complement nonempty there is an edge $e$ with $\mathrm{src}\,e \in S$ if and only if $\mathrm{tgt}\,e \notin S$. Let $N$ be a positive natural number. Put $V := \mathrm{Fin}\,n \sqcup \coprod_{e} \mathrm{Fin}\,(W_e - 1)$, the vertices of the graph obtained by subdividing edge $e$ into $W_e$ segments, the second summand indexing the interior subdivision points. The segments are indexed by pairs $\varepsilon = (e, i)$ with $i : \mathrm{Fin}\,(W_e)$, and $\mathrm{ends}\,\varepsilon$ is the pair whose first entry is $\mathrm{src}\,e$ when $i = 0$ and the interior point $(e, i-1)$ otherwise, and whose second entry is $\mathrm{tgt}\,e$ when $i + 1 = W_e$ and the interior point $(e, i)$ otherwise. For $v \in V$ set $\mathrm{lap}\,v := \sum_{\varepsilon} \big[ [\,(\mathrm{ends}\,\varepsilon)_1 = v\,](\delta_v - \delta_{(\mathrm{ends}\,\varepsilon)_2}) + [\,(\mathrm{ends}\,\varepsilon)_2 = v\,](\delta_v - \delta_{(\mathrm{ends}\,\varepsilon)_1}) \big] \in \mathbb{Z}^V$, where $\delta_w$ is the standard basis function; this is the row at $v$ of the combinatorial Laplacian of the subdivided graph. The conclusion is that in the quotient group $\mathbb{Z}^V / \langle \mathrm{lap}\,v : v \in V\rangle$ the subgroup of elements $x$ with $N \cdot x = 0$ is finite, and its cardinality satisfies $\#\{x : N x = 0\} \cdot N^n \le N^{m+1}$.
--
--   The quotient $\mathbb{Z}^V$ modulo the image of the Laplacian is the Jacobian (critical group, or component group of the Néron model in the semistable setting) of the subdivided graph, extended by a free rank-one factor; the inequality is the bound $\#\mathrm{Jac}[N] \le N^{b_1}$ by the cycle rank $b_1 = m - n + 1$, stated multiplicatively so as to avoid truncated subtraction. It feeds the analysis of the component group and of divisor classes attached to a semistable covering in [`AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.SemistableCovering.natCard_torsion_quotient_lap_mul_pow_le_pow_of_forall_exists_src_mem_iff
    (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S))
    (N : ℕ) (hN : 0 < N) :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    Finite {x : (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap) // ((N : ℕ) : ℤ) • x = 0} ∧
      Nat.card {x : (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap) // ((N : ℕ) : ℤ) • x = 0} * N ^ n ≤
        N ^ (m + 1) := by sorry
