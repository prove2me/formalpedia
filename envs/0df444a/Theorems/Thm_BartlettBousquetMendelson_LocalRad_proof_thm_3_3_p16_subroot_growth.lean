-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_proof_thm_3_3_p16_subroot_growth
-- name    : BartlettBousquetMendelson.LocalRad.proof_thm_3_3_p16_subroot_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:01:25.518085+00:00
-- url     : https://prove2.me/theorems/2c27e0c3-1c2a-40a3-8e75-bd24cdae8f49
-- title:
--   Growth of a sub-root function: $\psi(\beta r)\le\sqrt\beta\,\psi(r)$ and $\psi(r)\le\sqrt{rr^*}$ (proof of Theorem 3.3, p. 16)
-- statement:
--   Let $\psi$ be a sub-root function. Then
--
--   1. for every $r\ge0$ and $\beta\ge1$,
--   $$
--   \psi(\beta r)\le\sqrt\beta\,\psi(r);
--   $$
--   2. if $r^*>0$ is a fixed point of $\psi$, then for every $r\ge r^*$,
--   $$
--   \psi(r)\le\sqrt{r/r^*}\,\psi(r^*)=\sqrt{rr^*}.
--   $$
--
--   These two inequalities let the proof of Theorem 3.3 replace $\psi(r)$ by a multiple of $\sqrt{rr^*}$.
--
--   Differences from the source:
--   - generalization: ψ a (nontrivial) sub-root function → ψ any sub-root function (IsSubRoot); reason: the paper's ψ is nontrivial; the claims hold for every sub-root ψ, so they specialize to the paper's
--   - encoding: r* the fixed point of ψ → any r* > 0 with ψ r* = r*; reason: unique by Lemma 3.2
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), proof of Theorem 3.3, first part, p. 16 (unnumbered) (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsSubRoot

namespace BartlettBousquetMendelson.LocalRad

/-- **Growth of a sub-root function (proof of Theorem 3.3, first part, p. 16; unnumbered).**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), proof of Theorem 3.3, first part, p. 16: "By our assumption it follows that for β ≥ 1,
ψ(βr) ≤ √β ψ(r)." and "Moreover, for r ≥ r∗, ψ(r) ≤ √(r/r∗) ψ(r∗) = √(rr∗)".

For a sub-root `ψ`: (1) `ψ(β r) ≤ √β ψ(r)` for all `r ≥ 0` and `β ≥ 1`; (2) if `r* > 0` is a
fixed point (`ψ r* = r*`), then `ψ r ≤ √(r r*)` for every `r ≥ r*`.

**Formalization Note.** The paper states (1) for the `r ≥ 0` at which it applies it; at `r = 0`
it reads `ψ(0) ≤ √β ψ(0)`, true since `ψ(0) ≥ 0`. -/
theorem proof_thm_3_3_p16_subroot_growth (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) :
    (∀ r β : ℝ, 0 ≤ r → 1 ≤ β → ψ (β * r) ≤ Real.sqrt β * ψ r) ∧
      ∀ rstar : ℝ, 0 < rstar → ψ rstar = rstar →
        ∀ r : ℝ, rstar ≤ r → ψ r ≤ Real.sqrt (r * rstar) := by sorry

end BartlettBousquetMendelson.LocalRad
