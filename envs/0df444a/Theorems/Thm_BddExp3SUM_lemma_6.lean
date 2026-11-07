-- Prove2me | Theorems.Thm_BddExp3SUM_lemma_6
-- name    : BddExp3SUM.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:01:07.390409+00:00
-- url     : https://prove2.me/theorems/ebf6fe3d-08fb-48b5-aa37-b224f399c80f
-- title:
--   Lemma 6: a product entry is positive exactly when $K(x_1+x_2+x_3)=0$; at most $F$ positive probes contain no true witness
-- statement:
--   All differences $K(x)-K(z_b)$, $x\in b$, lie in $B$, and for a probe $Q$ the element $w_Q$ lies in $B$ with a unique decomposition $(\mu_1,\mu_2)$.
--
--   For a probe $Q=(x_1;b_2,b_3)$, the product entry at $((b_2,\mu_1),(b_3,\mu_2))$ is positive exactly when some pair $x_2\in b_2$, $x_3\in b_3$ satisfies
--
--   $$K(x_1+x_2+x_3)=0.$$
--
--   Every true witness has a positive probe, and at most $F$ positive probes contain no true witness.
--
--   So the matrix call locates witnesses, with a number of false alarms the scan cap can absorb.
--
--   **Formalization Note** The last clause is stated for every finite family of positive probes containing no true witness.
--
--   Differences from the source:
--   - encoding: 0/1 matrices X ∈ Z^{N×D}, Y ∈ Z^{D×N} padded to size N → functions on (block × B₁) × B and B × (block × B₂); the entry of XY is the sum over λ ∈ B; reason: padding adds only zero rows and columns; the room for it is a clause of the (14)–(16) item
--   - reading: the blocks "given by Lemma 3" → any block cut in the sense of IsBlockCut, with any representatives z_b ∈ b; reason: the source’s "choose a representative" is arbitrary; the cut is as in Lemma 3
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 6, p.5, with (12), (13) (PDF p.6)

import Mathlib
import Definitions.Def_BddExp3SUM_Blocks

namespace BddExp3SUM

/-- Lemma 6, p.5, with the definitions (12), (13) and the decomposition of `w_Q` above it (Zeng, Wang,
Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…).

**Formalization Note.** Clause by clause: the differences lie in `B`; `w_Q` lies in `B` and decomposes
uniquely; a product entry for a probe is positive exactly when some pair has `K(x₁ + x₂ + x₃) = 0`;
every true witness has a positive probe; at most `F` positive probes contain no true witness. -/
theorem lemma_6 {M r n k q e p : ℕ} [NeZero M] {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) (u : Fin (k + q) → Grp M r)
    (parts₂ parts₃ : Finset (Finset (Grp M r)))
    (hb₂ : IsBlockCut (piHash h.p_dvd e u) (U 1) (σ M n) parts₂)
    (hb₃ : IsBlockCut (piHash h.p_dvd e u) (U 2) (σ M n) parts₃)
    (z : Finset (Grp M r) → Grp M r) (hz₂ : ∀ b ∈ parts₂, z b ∈ b) (hz₃ : ∀ b ∈ parts₃, z b ∈ b) :
    let K := KHash e u
    let Pr := probes (piHash h.p_dvd e u) (U 0) parts₂ parts₃ z
    let A := B M r e k q p
    let A₁ := B₁ M r e k q p
    let A₂ := B₂ M r e k q p
    (∀ b ∈ parts₂ ∪ parts₃, ∀ x ∈ b, K x - K (z b) ∈ A) ∧
    (∀ Q ∈ Pr, wProbe K z Q ∈ A ∧
      ∃! v : A₁ × A₂, (v.1 : KTarget M r e k q) + v.2 = wProbe K z Q) ∧
    (∀ Q ∈ Pr, ∀ (μ₁ : A₁) (μ₂ : A₂), (μ₁ : KTarget M r e k q) + μ₂ = wProbe K z Q →
      (0 < supportEntry K z A₁ A₂ A (Q.2.1, μ₁) (Q.2.2, μ₂) ↔
        ∃ x₂ ∈ Q.2.1, ∃ x₃ ∈ Q.2.2, K (Q.1 + x₂ + x₃) = 0)) ∧
    (∀ x₁ ∈ U 0, ∀ x₂ ∈ U 1, ∀ x₃ ∈ U 2, x₁ + x₂ + x₃ = 0 →
      ∃ b₂ ∈ parts₂, ∃ b₃ ∈ parts₃, x₂ ∈ b₂ ∧ x₃ ∈ b₃ ∧ (x₁, b₂, b₃) ∈ Pr ∧
        IsPositiveProbe K z A₁ A₂ A (x₁, b₂, b₃)) ∧
    ∀ Qs : Finset (Grp M r × Finset (Grp M r) × Finset (Grp M r)),
      (∀ Q ∈ Qs, Q ∈ Pr ∧ IsPositiveProbe K z A₁ A₂ A Q ∧
        ¬ ∃ x₂ ∈ Q.2.1, ∃ x₃ ∈ Q.2.2, Q.1 + x₂ + x₃ = 0) →
      Qs.card ≤ countFalse U K := by sorry

end BddExp3SUM
