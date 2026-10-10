-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_differentiableOn_eq_heckeLSeries
-- name    : ArtinPrimitiveRoots.exists_differentiableOn_eq_heckeLSeries
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T10:46:47.842461+00:00
-- url     : https://prove2.me/theorems/0a9ab1b4-f75d-4bd3-ba9e-82ec43e9d927
-- title:
--   §8.3 of OpenAI's Primitive roots paper — Hecke continuation: L(s, χ) of a finite-order Hecke character is holomorphic on s ≠ 1
-- statement:
--   Let $F$ be a number field, $\mathfrak m$ a nonzero ideal of $\mathcal O_F$ and $\chi$ a finite-order Hecke character of $F$ of modulus $\mathfrak m$ (`HeckeChar F 𝔪`). Then there is a function $g : \mathbb C \to \mathbb C$, holomorphic on $\{s : s \ne 1\}$, that agrees with the Hecke $L$-series $L(s, \chi) = \sum_{\mathfrak a}\chi(\mathfrak a)\,\mathrm N\mathfrak a^{-s}$ (`χ.LSeries`) on $\operatorname{Re} s > 1$.
--
--   This is Hecke's theorem: the $L$-series of a nontrivial ray class character is entire, and for the trivial character it is the Dedekind zeta function times finitely many Euler factors. The paper uses it, as “the Hecke continuation”, to make $\mathscr A(s) = e^{(s-5/6)^2}\mathcal H_\eta(s)/L^S(s, \eta)$ meromorphic in the last step of the proof of Theorem 1.2.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 60: “For $\operatorname{Re} s > 1 - 1/20000$, the second neighborhood in Theorem 7.3 makes the numerator $e^{(s-5/6)^2}\mathcal H_\eta(s)$ holomorphic and nowhere zero. The Hecke continuation makes $\mathscr A(s)$ meromorphic there.” and p. 16: “The latter notation also denotes the usual meromorphic continuation of this incomplete Hecke $L$-function; a principal pole is permitted.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 16, 60, proof of Theorem 1.2, §8.3 (the Hecke continuation)

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_differentiableOn_eq_heckeLSeries (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s | s ≠ 1} ∧ ∀ s : ℂ, 1 < s.re → g s = χ.LSeries s := by
  sorry

end ArtinPrimitiveRoots
