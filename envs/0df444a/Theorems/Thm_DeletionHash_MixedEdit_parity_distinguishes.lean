-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_parity_distinguishes
-- name    : DeletionHash.MixedEdit.parity_distinguishes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:29.504225+00:00
-- url     : https://prove2.me/theorems/8b2a09df-9fd1-4c78-a11f-c3d2d6bcaec3
-- title:
--   Lemma 3.3 — parity distinguishes
-- statement:
--   In the standing proof regime $q\ge2$, $t\ge2$, $b\ge1$, $k=2\lceil\log_q n\rceil+2$, $L=3(k+b+1)$, $k>b$ and $n\ge L$, let $x$ be an $(L-1)$-unique word of length $n$. Every distinct word $z$ of that length satisfies
--   $$\overline{R_L(z)-R_L(x)}\ne0.$$
--   The partner $z$ has no uniqueness assumption. The statement makes the nonzero-difference probability estimate applicable to every same-length exceptional partner.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 3.3, printed p. 10 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 3.3: the partner is an arbitrary word of the same length. -/
theorem parity_distinguishes {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique (L-1) (letters x)) :
    ∀ z : Word α n, z ≠ x → parity (spectrum L (letters z) - spectrum L (letters x)) ≠ 0 := by sorry

end DeletionHash.MixedEdit
