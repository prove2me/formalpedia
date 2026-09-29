-- Prove2me | Theorems.Thm_ArithmeticE_irreducible_spanning_orbit_factor
-- name    : ArithmeticE.irreducible_spanning_orbit_factor
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T20:53:39.166606+00:00
-- url     : https://prove2.me/theorems/d6dff768-7add-4b75-8bee-42c55dfdad41
-- title:
--   A vanishing product on an irreducible family kills one spanning evaluation functional
-- statement:
--   Let $H$ be an irreducible topological space and let $V_i$ be finitely many complex vector spaces. Suppose maps $o_i:H\to V_i$ have images spanning $V_i$, and let $\ell_i:V_i\to\mathbb C$ be linear. Assume each set
--   $$Z_i=\{h\in H:\ell_i(o_i(h))=0\}$$
--   is closed. If $\prod_i\ell_i(o_i(h))=0$ for every $h$, then one of the functionals $\ell_i$ is identically zero.
--
--   The zero-product hypothesis covers $H$ by finitely many closed sets $Z_i$. Irreducibility forces one $Z_i$ to be all of $H$. The corresponding functional kills the spanning image of $o_i$, hence the entire vector space.
--
--   This is the topological and linear-algebra step in Beukers' conjugate-product argument. For its differential Galois application, the irreducible group, closed orbit zero sets, spanning property, and product-vanishing statement must still be constructed and proved; this theorem does not assume those arithmetic prerequisites have been formalized.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, proof of Theorem 2.5, p. 5, finite union of the closed sets H_i and the orbit-spanning conclusion.

import Mathlib

theorem ArithmeticE.irreducible_spanning_orbit_factor {H : Type*} [TopologicalSpace H] [IrreducibleSpace H]
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (orbit : ∀ i, H → V i) (ev : ∀ i, V i →ₗ[ℂ] ℂ)
    (hspan : ∀ i, Submodule.span ℂ (Set.range (orbit i)) = ⊤)
    (hclosed : ∀ i, IsClosed {g : H | ev i (orbit i g) = 0})
    (hprod : ∀ g, ∏ i, ev i (orbit i g) = 0) :
    ∃ i, ev i = 0 := by sorry
