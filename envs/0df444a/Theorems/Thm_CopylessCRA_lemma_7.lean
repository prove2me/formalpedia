-- Prove2me | Theorems.Thm_CopylessCRA_lemma_7
-- name    : CopylessCRA.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:43.973197+00:00
-- url     : https://prove2.me/theorems/4cf8b428-5fd0-46b3-bac4-fc4a50460524
-- title:
--   Lemma 7, p.8 — $u=\sum_{j<d}\binom{1/t}{j}(u^t-I)^j$; roots of unipotents commute with what commutes with powers
-- statement:
--   Let $t\ge1$.
--
--   1. If $u$ is a unipotent $d\times d$ rational matrix, then
--   $$u=\sum_{j=0}^{d-1}\binom{1/t}{j}(u^t-I)^j ,$$
--   where $\binom{1/t}{j}$ is the generalized binomial coefficient; in particular $u$ commutes with every matrix commuting with $u^t$.
--   2. If $g$ is an invertible rational matrix with unipotent Jordan part $g_u$, then $(g_u)^t$ is the unipotent Jordan part of $g^t$, i.e. $(g^t)_u=(g_u)^t$, and $g_u$ commutes with every matrix commuting with $(g^t)_u$.
--
--   Differences from the source:
--   - encoding: $\binom{1/t}{j}$ → `Ring.choose (1/t) j` in $\mathbb Q$; reason: Mathlib's generalized binomial coefficient: $j!\binom{r}{j}=r(r-1)\cdots(r-j+1)$; checked $\binom{1/2}{2}=-1/8$ in the verification file
--   - encoding: $g$ (a matrix with Jordan parts, context (A2): $g\in GL_d(\mathbb Q)$) → $g$ an invertible rational matrix, $g_u$ given by the Jordan relation; reason: the paper's $g$ ranges over $GL_d(\mathbb Q)$, where the multiplicative Jordan decomposition is defined and unique
--   - encoding: the unipotent Jordan part $g_u$ → a relation: $u$ is unipotent, commutes with a semisimple $s$, and $g=su$; reason: the Jordan decomposition is unique, so for invertible $g$ exactly one $u$ qualifies
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Lemma 7, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_CopylessCRA_zariskiClosure

namespace CopylessCRA

/-- **Lemma 7.** If `u` is a unipotent `d × d` rational matrix and `t ≥ 1`, then
`u = ∑_{j=0}^{d−1} binom(1/t, j) (u^t − I)^j`. In particular `u` commutes with every matrix
commuting with `u^t`, and `g_u` commutes with every matrix commuting with `(g^t)_u = (g_u)^t`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Lemma 7, p.8 (PDF p.10).

**Formalization Note** `binom(1/t, j)` is the generalized binomial coefficient `Ring.choose (1/t) j`
in `ℚ`. `g` is an invertible rational matrix (the setting of (A2), p.6) and `g_u` its unipotent
Jordan part over `ℚ`, given as a relation (`IsUnipotentJordanPart`); "`(g^t)_u = (g_u)^t`" says that
`(g_u)^t` is the unipotent Jordan part of `g^t`. -/
theorem lemma_7 {d : ℕ} (t : ℕ) (ht : 1 ≤ t) :
    (∀ u : Matrix (Fin d) (Fin d) ℚ, IsUnipotent u →
      u = ∑ j ∈ Finset.range d, Ring.choose (1 / (t : ℚ)) j • (u ^ t - 1) ^ j ∧
      ∀ A : Matrix (Fin d) (Fin d) ℚ, Commute A (u ^ t) → Commute A u) ∧
    ∀ g gu : Matrix (Fin d) (Fin d) ℚ, IsUnit g → IsUnipotentJordanPart g gu →
      IsUnipotentJordanPart (g ^ t) (gu ^ t) ∧
      ∀ A : Matrix (Fin d) (Fin d) ℚ, Commute A (gu ^ t) → Commute A gu := by sorry

end CopylessCRA
