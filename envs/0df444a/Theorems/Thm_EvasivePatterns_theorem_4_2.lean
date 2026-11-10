-- Prove2me | Theorems.Thm_EvasivePatterns_theorem_4_2
-- name    : EvasivePatterns.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:26.705985+00:00
-- url     : https://prove2.me/theorems/906b05e2-a8e3-456a-a1a4-a06fb1145316
-- title:
--   Theorem 4.2 — a unique non-reciprocal irreducible factor, simple and irreducible over $\mathbb Q(\zeta)$
-- statement:
--   Let $Q \in \mathbb Z[z]$ satisfy the hypotheses of Lemma 4.1: constant coefficient $1$, nonzero coefficients in $\{\pm 1\}$, rigid support $S$ and $\|QQ^*\|_1 = |S|^2$. If $Q$ is not reciprocal, then:
--
--   1. $Q$ has exactly one irreducible non-reciprocal factor $F \in \mathbb Q[z]$ (normalized monic);
--   2. $F$ occurs with multiplicity one: $F^2 \nmid Q$;
--   3. $F$ remains irreducible over every finite Galois extension $K/\mathbb Q$, $K \subseteq \mathbb C$, in which complex conjugation is central;
--   4. in particular $F$ remains irreducible over every cyclotomic field $\mathbb Q(\zeta)$.
--
--   This distinguished factor, rather than $Q$ itself, is what resists factorization after adjoining roots of unity; for $Q_{01100} = (1+z+z^2)(z^3-z+1)$ it is $z^3 - z + 1$.
--
--   Differences from the source:
--   - encoding: exactly one irreducible non-reciprocal factor F ∈ ℚ[z] → exactly one monic irreducible non-reciprocal divisor F; reason: factors are counted up to associates; the proof normalizes F monic (p.6, line 195)
--   - encoding: with multiplicity one → F² does not divide Q; reason: same content
--   - encoding: rigid support (every homometric finite set is a translate of S or of its reflection) → Rigid, quantified over nonempty finite integer sets; reason: the notions differ only for a one-point support, i.e. Q = 1, which is reciprocal and so fails the hypothesis that Q is not reciprocal; no instance changes
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Theorem 4.2, p.6 (PDF p.7), lines 182–185

import Mathlib
import Definitions.Def_EvasivePatterns_Rigid
import Definitions.Def_EvasivePatterns_l1Norm
import Definitions.Def_EvasivePatterns_IsCentralConjGalois
import Definitions.Def_EvasivePatterns_IsReciprocal

namespace EvasivePatterns

/-- **Theorem 4.2 (A unique cyclotomically irreducible non-reciprocal factor).** Under the
hypotheses of Lemma 4.1, if `Q` is not reciprocal, it has exactly one irreducible non-reciprocal
factor `F ∈ ℚ[z]`, with multiplicity one. This factor remains irreducible over every finite Galois
extension `K/ℚ` in which complex conjugation is central; in particular, it remains irreducible over
every cyclotomic field `ℚ(ζ)`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Theorem 4.2, printed p. 6 (PDF p. 7), lines 182–185.

**Formalization Note** The hypotheses of Lemma 4.1 on `Q`: constant coefficient `1`, nonzero
coefficients `±1`, rigid support (cast to `ℤ`), `‖QQ^*‖₁ = |S|²`. `Q` is viewed in `ℚ[z]` by the
coefficient cast. "Exactly one" factor is up to associates, so `F` is normalized monic (as in the
proof, p. 6, line 195): `F` is the unique monic irreducible non-reciprocal divisor. Multiplicity one
is `F² ∤ Q`. The field class is `IsCentralConjGalois`; a cyclotomic field is `ℚ(ζ) ⊆ ℂ` for a root of
unity `ζ` (`ζⁿ = 1`, `n > 0`), stated separately as printed. -/
theorem theorem_4_2 (Q : Polynomial ℤ) (hQ0 : Q.coeff 0 = 1)
    (hQpm : ∀ i, Q.coeff i ≠ 0 → Q.coeff i = 1 ∨ Q.coeff i = -1)
    (hrigid : Rigid (Q.support.image (fun n : ℕ => (n : ℤ))))
    (hnorm : l1Norm (Q * Q.reverse) = (Q.support.card : ℤ) ^ 2)
    (hnrec : ¬ IsReciprocal (Q.map (Int.castRingHom ℚ))) :
    ∃ F : Polynomial ℚ,
      (F.Monic ∧ Irreducible F ∧ ¬ IsReciprocal F ∧ F ∣ Q.map (Int.castRingHom ℚ)) ∧
      (∀ G : Polynomial ℚ, G.Monic → Irreducible G → ¬ IsReciprocal G →
        G ∣ Q.map (Int.castRingHom ℚ) → G = F) ∧
      ¬ F ^ 2 ∣ Q.map (Int.castRingHom ℚ) ∧
      (∀ K : IntermediateField ℚ ℂ, IsCentralConjGalois K →
        Irreducible (F.map (algebraMap ℚ K))) ∧
      (∀ (ζ : ℂ) (n : ℕ), 0 < n → ζ ^ n = 1 →
        Irreducible (F.map (algebraMap ℚ (IntermediateField.adjoin ℚ ({ζ} : Set ℂ))))) := by sorry

end EvasivePatterns
