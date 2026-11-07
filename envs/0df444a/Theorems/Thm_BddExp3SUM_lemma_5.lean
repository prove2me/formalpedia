-- Prove2me | Theorems.Thm_BddExp3SUM_lemma_5
-- name    : BddExp3SUM.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:01:20.367917+00:00
-- url     : https://prove2.me/theorems/507e9df0-24af-43d2-a1bd-d6beb878af80
-- title:
--   Lemma 5: $|\mathcal P|\le nC_2+2n^2/\sigma+Z_\pi/\sigma^2$, and $|\mathcal P|\le An^2/\sigma$ on the good event
-- statement:
--   Let $C_2$ be the number of nonempty $\pi$-classes in $U_2$. The set $\mathcal P$ of probes satisfies
--
--   $$|\mathcal P|\le nC_2+2n^2/\sigma+Z_\pi/\sigma^2.$$
--
--   On the good event (10), $|\mathcal P|\le An^2/\sigma$ for $A=M^2+3+24L$.
--
--   This bound is what makes the listing cap of the algorithm harmless on the good event.
--
--   **Formalization Note** Lists 1, 2, 3 are `U 0`, `U 1`, `U 2`. Divisions are in $\mathbb R$.
--
--   Differences from the source:
--   - reading: the blocks "given by Lemma 3" → any block cut in the sense of IsBlockCut, with any representatives z_b ∈ b; reason: the source’s "choose a representative" is arbitrary; the cut is as in Lemma 3
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 5, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_BddExp3SUM_Blocks

namespace BddExp3SUM

/-- Lemma 5, p.5 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…).

**Formalization Note.** The blocks are those of `IsBlockCut` in lists 2 and 3, which are `U 1` and
`U 2`, and `z` is any choice of representatives. All divisions are in `ℝ`. -/
theorem lemma_5 {M r n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) (u : Fin (k + q) → Grp M r)
    (parts₂ parts₃ : Finset (Finset (Grp M r)))
    (hb₂ : IsBlockCut (piHash h.p_dvd e u) (U 1) (σ M n) parts₂)
    (hb₃ : IsBlockCut (piHash h.p_dvd e u) (U 2) (σ M n) parts₃)
    (z : Finset (Grp M r) → Grp M r) (hz₂ : ∀ b ∈ parts₂, z b ∈ b) (hz₃ : ∀ b ∈ parts₃, z b ∈ b) :
    ((probes (piHash h.p_dvd e u) (U 0) parts₂ parts₃ z).card : ℝ) ≤
      n * classCount (U 1) (piHash h.p_dvd e u) + 2 * (n : ℝ) ^ 2 / σ M n +
        countKer U (piHash h.p_dvd e u) / (σ M n : ℝ) ^ 2 ∧
    (GoodEvent n U (piHash h.p_dvd e u) (KHash e u) →
      ((probes (piHash h.p_dvd e u) (U 0) parts₂ parts₃ z).card : ℝ) ≤
        Acoef M * (n : ℝ) ^ 2 / σ M n) := by sorry

end BddExp3SUM
