-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_annihilator_generator_degree
-- name    : ApproxPolySatCH.Main.annihilator_generator_degree
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:03.705344+00:00
-- url     : https://prove2.me/theorems/24e99f83-eaf6-4d7d-8c8d-3e8220826bd3
-- title:
--   Claim 7 — Perron bound for the annihilator generator
-- statement:
--   For a minimally dependent $f=(f_1,\ldots,f_{n+1})$ with $n\ge1$, any generator $H$ of its substitution kernel satisfies
--   $$\deg H\le \prod_{i=1}^{n+1}\deg f_i\le \max(\deg f_1,\ldots,\deg f_{n+1})^{n+1}.$$
--   The right-hand side is the `maxDegree` expression used by the formal interface. The first inequality is Perron's degree bound, and the second follows because every $\deg f_i\le\max_j\deg f_j$ and $n+1>0$. Since Perron supplies a nonzero member of the kernel, $H$ is nonzero and divides it, which yields the bound on $\deg H$.
-- source:
--   STOC 2027 submission #1125, Claim 7 and proof, p.18, citing Płonka [Plo05, Theorem 1.1].

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

theorem ApproxPolySatCH.Main.annihilator_generator_degree {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f) (H : Poly k (n + 1))
    (hker : annihilator f = Ideal.span {H}) :
    H.totalDegree ≤ maxDegree f ^ (n + 1) := by sorry
