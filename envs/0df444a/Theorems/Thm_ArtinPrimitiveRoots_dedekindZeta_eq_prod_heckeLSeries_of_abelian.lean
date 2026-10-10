-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_dedekindZeta_eq_prod_heckeLSeries_of_abelian
-- name    : ArtinPrimitiveRoots.dedekindZeta_eq_prod_heckeLSeries_of_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T07:13:07.408899+00:00
-- url     : https://prove2.me/theorems/4e03429e-2daf-406d-a546-17f5b5d18b31
-- title:
--   Neukirch VII (10.5)–(10.6) — over a totally complex base, the Dedekind zeta function of an abelian extension is a product of Hecke L-series
-- statement:
--   Let $F$ be a totally complex number field (`IsTotallyComplex F`: no real places), and let $L$ be a number field that is an $F$-algebra, Galois over $F$, with commutative Galois group ($\sigma\tau = \tau\sigma$ for all $\sigma, \tau \in \operatorname{Gal}(L/F)$). Then there are $n \in \mathbb N$, nonzero ideals $\mathfrak m_1, \dots, \mathfrak m_n$ of $\mathcal O_F$, and finite-order Hecke characters $\eta_i$ of $F$ of modulus $\mathfrak m_i$ (`HeckeChar F 𝔪ᵢ`, from the bundle `Def_ArtinHecke`) with
--
--   $$\zeta_L(s) = \prod_{i=1}^n L(s, \eta_i)\qquad(\operatorname{Re} s > 1),$$
--
--   where $\zeta_L$ is Mathlib's Dedekind zeta function and $L(s, \eta_i)$ is the bundle's `HeckeChar.LSeries`, the $L$-series of $n \mapsto \sum_{N\mathfrak a = n}\eta_i(\mathfrak a)$.
--
--   In Neukirch's Theorem (10.6) the factors are the Hecke $L$-series of the primitive ray class characters attached by the Artin map to the $[L : F]$ characters of $\operatorname{Gal}(L/F)$, the $\mathfrak m_i$ being their conductors. The hypothesis that $F$ is totally complex is there because the bundle's Hecke characters carry no sign conditions at real places: each is a character of the ideals prime to $\mathfrak m_i$, trivial on every principal ideal $(\alpha)$ with $\alpha \equiv 1 \pmod{\mathfrak m_i}$. The statement asserts only that such a family exists.
--
--   A cut for `kummer_zero_free_of_hecke` (the descent (9.2) in the proof of Lemma 9.1 of OpenAI's *Primitive roots for every admissible integer base*, p. 61). There it is applied to the cyclic extension $\widetilde K = \mathbb Q(\mu_{12q}, a^{1/q})$ of $F = \mathbb Q(\mu_{12q})$, which is the paper's factorization (9.3).
--
--   J. Neukirch, *Algebraic Number Theory*, Grundlehren der mathematischen Wissenschaften 322, Springer, 1999, Chapter VII, Corollary (10.5) and Theorem (10.6), [doi:10.1007/978-3-662-03983-0](https://doi.org/10.1007/978-3-662-03983-0); cited for (9.3)–(9.4) by OpenAI's paper, p. 61.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren der mathematischen Wissenschaften 322, Springer, 1999, https://doi.org/10.1007/978-3-662-03983-0, p. 419–549, Chapter VII, Corollary (10.5) and Theorem (10.6) (abelian Artin factorization; cited for (9.3)–(9.4) of OpenAI, Primitive roots for every admissible integer base, p. 61)

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField

theorem dedekindZeta_eq_prod_heckeLSeries_of_abelian (F L : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L]
    (hab : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ) :
    ∃ (n : ℕ) (𝔪 : Fin n → Ideal (𝓞 F)), (∀ i, 𝔪 i ≠ ⊥) ∧
      ∃ η : (i : Fin n) → HeckeChar F (𝔪 i),
        ∀ s : ℂ, 1 < s.re → dedekindZeta L s = ∏ i, (η i).LSeries s := by
  sorry

end ArtinPrimitiveRoots
