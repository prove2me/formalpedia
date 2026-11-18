-- Prove2me | Theorems.Thm_BddExp3SUM_section_2_embedding_exact
-- name    : BddExp3SUM.section_2_embedding_exact
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-17T17:26:47.758465+00:00
-- url     : https://prove2.me/theorems/43c12f7e-3c20-45e2-afa6-c073ec64ac3f
-- title:
--   Section 2 — exact divisor embedding into Z_M (definition separated)
-- statement:
--   Let $M\ge2$. For every $m\mid M$, the map $f:\mathbb Z_m\to\mathbb Z_M$, $f(y)=(M/m)y$, is an injective additive homomorphism. Consequently, for an instance with moduli $m_1,\dots,m_r$, the coordinatewise map $a\mapsto((M/m_j)a_j)_j$ into $\mathbb Z_M^r$ is injective on residue vectors, and
--
--   $$a^{(1)}+a^{(2)}+a^{(3)}=0\text{ in }\prod_j\mathbb Z_{m_j}\iff\text{the embedded vectors sum to }0\text{ in }\mathbb Z_M^r.$$
--
--   This reduces every instance to the single ambient group $G=\mathbb Z_M^r$ with the same witnesses.
--
--   Differences from the source:
--   - encoding: residue vectors in ∏ Z_{m_j} → vectors of natural numbers a with a_j < m_j, as in the Instance structure; the zero-sum equivalence holds for any such natural vectors; reason: this is the input format of the goal theorem
--
--   Formalization repair: the map Instance.embed is imported from a separate definition instead of being declared before the theorem inside formal_statement. Every binder, hypothesis, and conclusion is unchanged from public theorem 669c2bc4-9724-4eaf-839a-9ed9618a8f10. The separation fixes the server target-type parser error reported on both submissions 738337ab-037e-45e7-8b60-266176bf6d3a and cb64230e-63ae-434a-ae3a-7e486229a559; it is not a weakening of the mathematical claim.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §2, p.1 (PDF p.2) Fixed PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1719.pdf, full SHA256 19546c9a7e1dc19337b43d433b0b3f7f97b6ecfae2578bc4d866441e305f6397. Mechanically identical proposition to public target 669c2bc4-9724-4eaf-839a-9ed9618a8f10, with the original map in an importable definition.

import Mathlib
import Definitions.Def_BddExp3SUM_Embedding

namespace BddExp3SUM

theorem section_2_embedding_exact (M : ℕ) (hM : 2 ≤ M) :
    (∀ m : ℕ, m ∣ M → ∃ f : ZMod m →+ ZMod M, Function.Injective f ∧
      ∀ y : ZMod m, f y = ((M / m * y.val : ℕ) : ZMod M)) ∧
    ∀ x : Instance M,
      (∀ a a' : Fin x.r → ℕ, (∀ j, a j < x.m j) → (∀ j, a' j < x.m j) →
        x.embed a = x.embed a' → a = a') ∧
      ∀ a₁ a₂ a₃ : Fin x.r → ℕ,
        x.ZeroSum a₁ a₂ a₃ ↔ x.embed a₁ + x.embed a₂ + x.embed a₃ = 0 := by sorry


end BddExp3SUM
