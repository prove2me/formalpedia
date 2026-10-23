-- Prove2me | Theorems.Thm_CircletTSP_Facet_window_le_two
-- name    : CircletTSP.Facet.window_le_two
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:09.794052+00:00
-- url     : https://prove2.me/theorems/bc2e7256-e90b-4da3-af27-fea2d0abd3ee
-- title:
--   Proof of Theorem 3.1, p. 12 — without the structures of Figure 4 every window has T_u ≤ 2
-- statement:
--   Let $n\ge 8$ be a multiple of $4$, $d=n/2$, and let $H$ be a Hamiltonian cycle on $K_n$ that contains none of the structures A, B1, B2 of Figure 4 at any vertex. Then for every vertex $u$,
--   $$T_u\le 2 .$$
--
--   $T_u=4$ would make the window a subtour, and $T_u=3$ means three edges of the window's $4$-cycle, which form one of the structures of Figure 4. Combined with the window count and Lemma 3.4 this gives $t_1+2t_d\le n$, contradicting Lemma 3.3.
--
--   **Formalization Note** The hypothesis "no structure at any vertex" is what Lemma 3.4 supplies ("for any $u\in[n]$"); it is needed in this form, since three window edges at $u$ may form structure A at $u+d$ rather than a structure at $u$. $n\ge 8$ is the page's "By Claim 3.2, $n\ge 8$" (p. 10).
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 12, proof of Theorem 3.1 ('By Lemma 3.4, T_u ≤ 2')

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Proof of Theorem 3.1 (p. 12): in a Hamiltonian cycle on `n ≥ 8` vertices containing none of
the structures A, B1, B2 of Figure 4 (at any vertex), every window count satisfies `T_u ≤ 2`. -/
theorem window_le_two (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hno : ∀ u : Fin n, ¬ IsStructA π u ∧ ¬ IsStructB1 π u ∧ ¬ IsStructB2 π u) :
    ∀ u : Fin n, window π u ≤ 2 := by sorry

end CircletTSP.Facet
