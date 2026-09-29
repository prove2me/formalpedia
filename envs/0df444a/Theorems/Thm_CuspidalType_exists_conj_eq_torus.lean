-- Prove2me | Theorems.Thm_CuspidalType_exists_conj_eq_torus
-- name    : CuspidalType.exists_conj_eq_torus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/0b4632c7-527d-53f5-a191-455c78607926
-- title:
--   Elements with no eigenvalue in 𝔽_q are conjugate into the non-split torus
-- statement:
--   Let $q$ be a prime and let $g$ be an element of `GL2 q`, the group $\mathrm{GL}_2(\mathbb{Z}/q)$ of invertible $2\times 2$ matrices over $\mathbb{Z}/q$. Assume that no element $x$ of $\mathbb{Z}/q$ is a root of the characteristic polynomial of the underlying matrix of $g$, i.e. $g$ has no eigenvalue in $\mathbb{Z}/q$. The assertion is that there exist $h$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ and a unit $\alpha$ of the field `GaloisField q 2` with $q^2$ elements such that $\alpha$, viewed in `GaloisField q 2`, does not lie in the range of the structure map $\mathbb{Z}/q \to$ `GaloisField q 2` (so $\alpha$ generates the quadratic extension), and such that $h g h^{-1}$ equals `torus q α`. Here `torus q` is the group homomorphism from the units of `GaloisField q 2` to $\mathrm{GL}_2(\mathbb{Z}/q)$ obtained by sending $\alpha$ to the matrix of the $\mathbb{Z}/q$-linear multiplication map $x \mapsto \alpha x$ on `GaloisField q 2` with respect to the fixed basis `quadBasis q`, the basis of `GaloisField q 2` over $\mathbb{Z}/q$ coming from the equality of its rank with $2$.
--
--   This is the standard classification statement that an element of $\mathrm{GL}_2(\mathbb{F}_q)$ with irreducible characteristic polynomial is conjugate to an element of the non-split (elliptic) torus $\mathbb{F}_{q^2}^\times \hookrightarrow \mathrm{GL}_2(\mathbb{F}_q)$, the conjugating element being read off from a basis $(v, gv)$. It is used in the analysis of cuspidal types, where it supplies the normal form behind the characteristic-polynomial computations and the comparison of linear equivalences, and in the summation over elliptic conjugacy classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_conj_eq_torus.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_conj_eq_torus (q : ℕ) [Fact q.Prime] (g : GL2 q)
    (hg : ∀ x : ZMod q, ¬ (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x) :
    ∃ (h : GL2 q) (α : (GaloisField q 2)ˣ),
      (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2)) ∧ h * g * h⁻¹ = torus q α := by sorry
