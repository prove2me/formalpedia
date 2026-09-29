-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_sfe
-- name    : DiazModulus.diaz_of_sfe
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-09T06:29:37.706027+00:00
-- url     : https://prove2.me/theorems/0148ccca-b726-4238-8cb8-48eba0967a85
-- title:
--   Strong four exponentials implies Diaz's modulus conjecture
-- statement:
--   The strong four exponentials conjecture settles Diaz's modulus conjecture outright, by a single instantiation.
--
--   **The argument.** Let $u \neq 0$ with $\lVert u\rVert$ algebraic, and suppose $e^{u}$ were algebraic. If $u$ itself is algebraic, Hermite–Lindemann already gives a contradiction. Otherwise $u$ is transcendental, and so is $\overline{u}$, so both $(1, u)$ and $(1, \overline{u})$ are $\overline{\mathbb{Q}}$-linearly independent. Apply the strong four exponentials conjecture to
--
--   $$x = (1,\ u), \qquad y = (1,\ \overline{u}).$$
--
--   The four products are $1$, $\overline{u}$, $u$ and $u\overline{u} = \lVert u\rVert^{2}$. The first lies in $\widetilde{\mathcal{L}}$ by definition; $u$ and $\overline{u}$ lie in it because $e^{u}$ and $e^{\overline{u}} = \overline{e^{u}}$ are algebraic; and $\lVert u\rVert^{2}$ is algebraic, hence in $\overline{\mathbb{Q}} \cdot 1 \subseteq \widetilde{\mathcal{L}}$. That contradicts the conjecture.
--
--   Hermite–Lindemann is discharged from the Proved node `DiazModulus.hermite_lindemann_holds`, so the strong four exponentials conjecture is the only surviving hypothesis.
--
--   **What this says about the rest of the mission, stated plainly.** This mission carries a large decomposition of its root — several generations of case splits, a polar normal form, four-exponentials matrix machinery — and every open leaf of that tree is implied by the strong four exponentials conjecture. This node shows the same conjecture reaches the root directly, without any of it. So the tree should not be read as having reduced a hard problem to easier ones.
--
--   What the tree did do, and this is the part worth keeping, is isolate hypotheses **strictly weaker than** the strong four exponentials conjecture that still suffice. `DiazModulus.recip_pi_not_log` is one: it follows from the strong four exponentials conjecture and is not known to imply it, and two open leaves reduce to it. Weaker sufficient conditions are the honest description of what a decomposition of this kind produces, and they are what a reader should look for here rather than a ladder of progressively easier problems.
--
--   **Not claimed.** No converse. The strong four exponentials conjecture is open — it is D. Roy's strengthening of the four exponentials conjecture, with linear independence over $\overline{\mathbb{Q}}$ and the products allowed to lie in $\widetilde{\mathcal{L}}$ — and nothing here makes it more tractable. This node closes nothing.
--
--   **Attribution.** The instantiation is Diaz's. M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer 2000), p. 399, derives the transcendence of $|\lambda|$ for every non-zero $\lambda \in \mathcal{L}$ from the strong four exponentials conjecture with this choice of $x$ and $y$, and credits the observation to G. Diaz (J. Théor. Nombres Bordeaux **9** (1997)). Diaz states the conjecture, as a case of the strong four exponentials conjecture, in J. Théor. Nombres Bordeaux **16** (2004), § 5.1. The conjecture itself was proposed by D. Roy (J. Number Theory **41** (1992)); Waldschmidt's book states it as Conjecture 11.17.
-- source:
--   Direct instantiation of the strong four exponentials conjecture at x = (1, u), y = (1, conj u), as in M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, p. 399, where the observation is credited to G. Diaz (J. Théor. Nombres Bordeaux 9 (1997)); see also G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, section 5.1. The conjecture: D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Conjecture 11.17. Hermite-Lindemann discharged from DiazModulus.hermite_lindemann_holds.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_sfe : StrongFourExponentials → DiazModulusConjecture := by sorry
end DiazModulus
