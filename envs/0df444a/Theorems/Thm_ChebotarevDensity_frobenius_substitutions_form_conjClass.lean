-- Prove2me | Theorems.Thm_ChebotarevDensity_frobenius_substitutions_form_conjClass
-- name    : ChebotarevDensity.frobenius_substitutions_form_conjClass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:15:28.076964+00:00
-- url     : https://prove2.me/theorems/9b935efb-deb1-4470-b675-b12e7eb630bb
-- title:
--   Frobenius substitutions of an unramified prime form one conjugacy class
-- statement:
--   Let $f\in\mathbb Z[X]$ be monic with discriminant $\Delta(f)\neq0$, let $K$ be its splitting field and $G=\mathrm{Gal}(K/\mathbb Q)$. Let $p$ be a prime with $p\nmid\Delta(f)$. Then the set of Frobenius substitutions of $p$,
--   $$\{\sigma\in G:\ \exists\,\mathfrak Q\subset\mathcal O_K \text{ prime}, p\in\mathfrak Q,\ \sigma(x)\equiv x^p \ (\mathrm{mod}\ \mathfrak Q)\ \forall x\in\mathcal O_K\},$$
--   is exactly one conjugacy class of $G$.
--
--   This is what makes the Frobenius substitution $\sigma_p$ well defined up to conjugacy. It packages the basic facts (a)–(c) about places over $p$ stated in the source: places over $p$ exist, any two differ by an element of $G$, and this element is unique when $p\nmid\Delta(f)$.
--
--   **Formalization Note** The source phrases the facts in terms of places $K\to\overline{\mathbb F}_p\cup\{\infty\}$; the formal statement uses the equivalent language of prime ideals of $\mathcal O_K$ above $p$.
-- source:
--   P. Stevenhagen and H. W. Lenstra, Jr., "Chebotarëv and his density theorem", The Mathematical Intelligencer 18 (1996), no. 2, 26–37, https://doi.org/10.1007/BF03027290, p. 33: basic facts (a)–(c) about places, and "if φ varies over the places over a fixed prime p, then Frob_φ ranges over a conjugacy class in G"

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField

namespace ChebotarevDensity

theorem frobenius_substitutions_form_conjClass (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpd : ¬ (p : ℤ) ∣ f.discr) :
    ∃ C : ConjClasses (GalGroup f), {σ : GalGroup f | IsFrobeniusAt f p σ} = C.carrier := by sorry

end ChebotarevDensity
