-- Prove2me | Theorems.Thm_CoDecompFO_root_evaluation
-- name    : CoDecompFO.root_evaluation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:17.284209+00:00
-- url     : https://prove2.me/theorems/8fcfc125-b913-41b7-bddd-8c5bfcdec4da
-- title:
--   Proof of Theorem 1.16, root test (corrected: alternating evaluation) — deciding at the root
-- statement:
--   For every structure $G$, every map $\pi:G\to P$ and every matrix $\psi$ on $[2\ell]$,
--   $$
--   G\models\forall x_1\exists y_1\cdots\forall x_\ell\exists y_\ell\;\psi(\vec x,\vec y)
--   \quad\Longleftrightarrow\quad \mathrm{eval}_\psi\big(\pi_*(S^{\mathrm{full}}[G])\big),
--   $$
--   where $\mathrm{eval}_\psi$ is alternating evaluation: $\mathrm{eval}_\psi(A)$ says at level $0$ that all hypotheses in $A$ satisfy $\psi$, and at a higher level that for every $x'$ and every personality $p$ in $A(x')$ some pair $(y',c)\in p$ has $\mathrm{eval}_\psi(c)$.
--
--   Taking $G=G[r]$ and $\pi=\pi_r$ gives the root test, and needs only the table at $r$.
--
--   Differences from the source:
--   - correction: accept when there is a supported hypothetical all of whose leaf hypotheses satisfy the quantifier-free part of φ → alternating evaluation of the one full-strategy table; reason: the corrected table has one entry per node, and the printed test on that entry rejects true sentences: the full strategy has losing responses, as on the two-bag instance of Observation 5.79
--   - generalization: the root bag with the projection from the partial limit → any structure G with any map π to any set; reason: the root is the case G = G[r], π = π_r
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), proof of Theorem 1.16, p.41

import Mathlib
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **The root test**, corrected to alternating evaluation (Bumpus et al., arXiv:2611.04658, held file
sha256 d550d7af…, proof of Theorem 1.16, p.41): "Finally, at the root we apply Lemma 5.78 and accept when
there is a supported hypothetical all of whose leaf hypotheses satisfy the quantifier-free part of φ."

For every structure `G` and every map `π : G → P`, `G ⊨ ∀x₁∃y₁ ⋯ ∀x_ℓ∃y_ℓ ψ` iff the projection of the
full strategy's induced hypothetical passes alternating evaluation.

**Formalization Note** The corrected table holds one hypothetical per node (Observation 5.79), so the
printed test on that entry would ask all leaves to satisfy `ψ`, and the full strategy has losing
responses. Alternating evaluation replaces it. The map `π` need not be surjective. -/
theorem root_evaluation {σ : Sig} (G P : Type) [σ.lang.Structure G] (π : G → P) (ℓ : ℕ)
    (ψ : σ.lang.BoundedFormula Empty (2 * ℓ)) (hψ : IsMatrix ψ) :
    AltSat (G := G) ψ ℓ [] ↔ eval ψ ℓ (push π ℓ (ind σ (2 * ℓ) ℓ (Strat.full G ℓ) [])) := by sorry

end CoDecompFO
