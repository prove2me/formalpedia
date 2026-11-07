-- Prove2me | Theorems.Thm_CopylessCRA_c3_iff_c4
-- name    : CopylessCRA.c3_iff_c4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:02.112099+00:00
-- url     : https://prove2.me/theorems/fe19149a-bfea-4381-a72e-3f3eb086ee65
-- title:
--   Appendix A, p.13 — proof of (C3)⇔(C4)
-- statement:
--   Let $M_a$ ($a\in\Sigma$, finite) be invertible rational $d\times d$ matrices, $\Gamma$ the group they generate and $\mathcal G\subseteq GL_d(\overline{\mathbb Q})$ its Zariski closure. Then the following are equivalent:
--
--   - (C3) $\mathcal G^\circ$ is triangularizable over $\mathbb Q$, and any two unipotent elements of $\mathcal G$ commute;
--   - (C4) $\Gamma$ has a subgroup of finite index that is triangularizable over $\mathbb Q$ and in which any two elements have commuting unipotent Jordan parts.
--
--   Differences from the source:
--   - generalization: letter matrices of the minimal representation of an invertible series $f$ → any finite family of invertible rational matrices; reason: the proof uses only that the $M_a$ are invertible and generate $\Gamma$; a minimal representation is a special case
--   - encoding: the unipotent Jordan part $g_u$ → a relation: $u$ is unipotent, commutes with a semisimple $s$, and $g=su$; reason: the Jordan decomposition is unique, so for invertible $g$ exactly one $u$ qualifies
--   - encoding: Zariski closure via polynomials in the entries and $\det^{-1}$ → polynomials in the entries, closed sets taken relative to $GL_d(\overline{\mathbb Q})$; reason: multiplying by a power of $\det$, a unit on $GL$, gives the same closed subsets of $GL$
--   - encoding: identity component $\mathcal G^\circ$ of the algebraic group → the union of all Zariski-connected subsets of $\mathcal G$ containing $1$ (the connected component of $1$); reason: this is the identity component of a linear algebraic group; its group and finite-index properties (A1) are theorems, not definitions
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Appendix A, p.13 (PDF p.15), "Proof of (C3)⇔(C4)"

import Mathlib
import Definitions.Def_CopylessCRA_zariskiClosure

namespace CopylessCRA

/-- **Proof of (C3)⇔(C4)** (App. A). For invertible letter matrices `M_a`: `𝒢°` is triangularizable
over `ℚ` and any two unipotent elements of `𝒢` commute if and only if `Γ` has a subgroup of finite
index that is triangularizable over `ℚ` and in which any two elements have commuting unipotent Jordan
parts.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Appendix A, p.13 (PDF p.15), "Proof of (C3)⇔(C4)".

**Formalization Note** The proof uses only that the `M_a` are invertible rational matrices
generating `Γ`, so the equivalence is stated for every such family, without a series `f` and without
minimality (a generalization; at a minimal representation it is the paper's (C3)⇔(C4)). -/
theorem c3_iff_c4 {α : Type*} [Fintype α] {d : ℕ} (M : α → Matrix (Fin d) (Fin d) ℚ)
    (hM : ∀ a, IsUnit (M a)) :
    C3 M ↔ C4 M := by sorry

end CopylessCRA
