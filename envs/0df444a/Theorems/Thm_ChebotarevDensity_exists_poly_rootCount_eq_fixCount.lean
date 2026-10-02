-- Prove2me | Theorems.Thm_ChebotarevDensity_exists_poly_rootCount_eq_fixCount
-- name    : ChebotarevDensity.exists_poly_rootCount_eq_fixCount
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T14:26:42.007133+00:00
-- url     : https://prove2.me/theorems/bb6e3b38-de26-49bd-bf9e-3adebe0346b0
-- title:
--   Roots modulo p of the polynomial of a subgroup count Frobenius fixed points
-- statement:
--   Let $f\in\mathbb Z[X]$ be monic with nonzero discriminant, let $K$ be its splitting field over $\mathbb Q$, $G=\operatorname{Gal}(K/\mathbb Q)$, and let $H\le G$ be a subgroup. Then there are a monic polynomial $g\in\mathbb Z[X]$, irreducible over $\mathbb Q$, and a finite set $N$ of primes such that for every prime $p\notin N$ and every Frobenius substitution $\sigma\in G$ of $p$,
--   $$\#\{x\in\mathbb F_p:\ g(x)=0\}=\#\{xH\in G/H:\ \sigma xH=xH\}.$$
--
--   Thus the number of roots modulo $p$ of a suitable polynomial attached to $H$ (the minimal polynomial of an algebraic integer generating the fixed field $K^H$) equals the number of fixed points of the Frobenius substitution on $G/H$.
--
--   **Formalization Note** The left side is `rootCount g p` and the right side is `fixCount H σ`; "Frobenius substitution of $p$" is `IsFrobeniusAt f p σ`.
-- source:
--   Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer 18 (1996), no. 2, pp. 32–34 (Theorem of Frobenius, decomposition types, cycle patterns) and Appendix, pp. 35–36

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField

namespace ChebotarevDensity

theorem exists_poly_rootCount_eq_fixCount (f : ℤ[X]) (hf : f.Monic) (hdisc : f.discr ≠ 0)
    (H : Subgroup (GalGroup f)) :
    ∃ (g : ℤ[X]) (N : Finset ℕ), g.Monic ∧ Irreducible (g.map (Int.castRingHom ℚ)) ∧
      ∀ p : ℕ, p.Prime → p ∉ N → ∀ σ : GalGroup f, IsFrobeniusAt f p σ →
        rootCount g p = fixCount H σ := by sorry

end ChebotarevDensity
