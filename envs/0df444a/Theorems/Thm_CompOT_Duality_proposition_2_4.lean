-- Prove2me | Theorems.Thm_CompOT_Duality_proposition_2_4
-- name    : CompOT.Duality.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:45.861728+00:00
-- url     : https://prove2.me/theorems/bb111300-f202-468c-8102-dc202c6d7f11
-- title:
--   Proposition 2.4, p. 382 — Kantorovich duality: L_C(a, b) = max over (f, g) ∈ R(C) of ⟨f, a⟩ + ⟨g, b⟩
-- statement:
--   Let $a \in \Sigma_n$ and $b \in \Sigma_m$ be histograms and let $C \in \mathbb R^{n\times m}$ be any cost matrix. The Kantorovich problem
--   $$L_C(a,b) = \min_{P\in\mathbf U(a,b)} \langle C, P\rangle$$
--   admits the dual
--   $$L_C(a,b) = \max_{(f,g)\in\mathbf R(C)} \langle f,a\rangle + \langle g,b\rangle, \qquad \mathbf R(C) = \{(f,g)\in\mathbb R^n\times\mathbb R^m : f\oplus g \le C\}.$$
--   Precisely: there exist a coupling $P \in \mathbf U(a,b)$ minimizing $\langle C,\cdot\rangle$ over $\mathbf U(a,b)$ and a pair $(f,g)\in\mathbf R(C)$ maximizing $\langle f,a\rangle+\langle g,b\rangle$ over $\mathbf R(C)$, and
--   $$\langle C,P\rangle = \langle f,a\rangle + \langle g,b\rangle.$$
--
--   The maximizing $(f,g)$ are the **Kantorovich potentials**. This is the finite-dimensional Kantorovich duality on which the dual algorithms of the book (dual ascent, auction, Sinkhorn's dual interpretation) rest.
--
--   **Formalization Note** Both the minimum and the maximum are claims of the book, so both attainments are asserted, through the predicates "optimal coupling" and "dual optimal" rather than through real infima/suprema. The histogram hypotheses are essential: if $\sum a \ne \sum b$ then $\mathbf U(a,b)$ is empty and the dual is unbounded.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 2.4, (2.20)–(2.21), p. 382

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- Proposition 2.4, p. 382 (Kantorovich duality (2.20)): for histograms `a ∈ Σ_n`, `b ∈ Σ_m` and
any cost matrix `C`, the minimum `L_C(a, b)` of (2.11) is attained by some `P ∈ U(a, b)`, the maximum
of `⟨f, a⟩ + ⟨g, b⟩` over `R(C)` is attained by some `(f, g)`, and the two values are equal. -/
theorem proposition_2_4 {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) :
    ∃ (P : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ),
      CompOT.Assignment.IsOptimalCoupling C a b P ∧ IsDualOptimal C a b f g ∧ CompOT.Assignment.frob C P = dualObj a b f g := by sorry

end CompOT.Duality
