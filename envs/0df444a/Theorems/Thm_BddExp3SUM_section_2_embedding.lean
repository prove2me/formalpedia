-- Prove2me | Theorems.Thm_BddExp3SUM_section_2_embedding
-- name    : BddExp3SUM.section_2_embedding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:45.415029+00:00
-- url     : https://prove2.me/theorems/669c2bc4-9724-4eaf-839a-9ed9618a8f10
-- title:
--   §2: the embedding $\mathbb Z_m\to\mathbb Z_M$, $x\mapsto (M/m)x$, preserves zero-sum witnesses
-- statement:
--   Let $M\ge2$. For every $m\mid M$, the map $f:\mathbb Z_m\to\mathbb Z_M$, $f(y)=(M/m)y$, is an injective additive homomorphism. Consequently, for an instance with moduli $m_1,\dots,m_r$, the coordinatewise map $a\mapsto((M/m_j)a_j)_j$ into $\mathbb Z_M^r$ is injective on residue vectors, and
--
--   $$a^{(1)}+a^{(2)}+a^{(3)}=0\text{ in }\prod_j\mathbb Z_{m_j}\iff\text{the embedded vectors sum to }0\text{ in }\mathbb Z_M^r.$$
--
--   This reduces every instance to the single ambient group $G=\mathbb Z_M^r$ with the same witnesses.
--
--   Differences from the source:
--   - encoding: residue vectors in ∏ Z_{m_j} → vectors of natural numbers a with a_j < m_j, as in the Instance structure; the zero-sum equivalence holds for any such natural vectors; reason: this is the input format of the goal theorem
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §2, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_BddExp3SUM_Profiles

namespace BddExp3SUM

/-- Embedding a residue vector of `∏_j Z_{m_j}` into `Z_M^r` by `x ↦ (M/m_j) x` in each coordinate. -/
def Instance.embed {M : ℕ} (x : Instance M) (a : Fin x.r → ℕ) : Grp M x.r :=
  fun j => ((M / x.m j * a j : ℕ) : ZMod M)

/-- §2, p.1 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…): "Embed
`Z_m` into `Z_M` by `x ↦ (M/m)x`. This is an injective homomorphism, so the embedded lists have
exactly the same zero-sum witnesses."

**Formalization Note.** The second and third clauses are on residue vectors of an `Instance`: the
embedding is injective on them, and it preserves and reflects zero sums. -/
theorem section_2_embedding (M : ℕ) (hM : 2 ≤ M) :
    (∀ m : ℕ, m ∣ M → ∃ f : ZMod m →+ ZMod M, Function.Injective f ∧
      ∀ y : ZMod m, f y = ((M / m * y.val : ℕ) : ZMod M)) ∧
    ∀ x : Instance M,
      (∀ a a' : Fin x.r → ℕ, (∀ j, a j < x.m j) → (∀ j, a' j < x.m j) →
        x.embed a = x.embed a' → a = a') ∧
      ∀ a₁ a₂ a₃ : Fin x.r → ℕ,
        x.ZeroSum a₁ a₂ a₃ ↔ x.embed a₁ + x.embed a₂ + x.embed a₃ = 0 := by sorry

end BddExp3SUM
