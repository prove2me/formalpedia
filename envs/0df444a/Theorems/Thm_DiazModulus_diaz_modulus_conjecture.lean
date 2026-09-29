-- Prove2me | Theorems.Thm_DiazModulus_diaz_modulus_conjecture
-- name    : DiazModulus.diaz_modulus_conjecture
-- status  : Open
-- author  : @carlok
-- created : 2026-09-07T06:46:50.676221+00:00
-- url     : https://prove2.me/theorems/ba87d640-a434-4533-84f9-257c023754c3
-- title:
--   Diaz's modulus conjecture
-- statement:
--   **The mission goal.** For every non-zero complex number $u$ whose modulus $|u|$ is algebraic, $e^{u}$ is transcendental.
--
--   Equivalently: no non-zero logarithm of an algebraic number has algebraic modulus. Diaz states it as
--
--   > « Soit $u \in \mathbb{C}\setminus\{0\}$ avec $|u| \in \bar{\mathbb{Q}}$ ; alors $\mathrm{e}^{u}$ est transcendant. »
--
--   Open. It is recorded as an open problem in M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Springer 2000), p. 399, where its derivation from the strong four exponentials conjecture is credited to Diaz, and Diaz states it as Conjecture C(|u|) in J. Théor. Nombres Bordeaux **16** (2004), § 5.1. It follows from Schanuel's conjecture and from the strong four exponentials conjecture — the two milestones `DiazModulus.diaz_of_schanuel` and `DiazModulus.diaz_of_strongFourExponentials_and_hermite_lindemann` establish those implications unconditionally — so anything that closes this node closes a case of both.
--
--   A word on what will not work, because it is easy to spend a long time on it. For a candidate $u$ one has $\bar u = |u|^{2}/u$ with $|u|^{2}$ algebraic, so complex conjugation on $\bar{\mathbb{Q}}(u)$ is a rational function of the generator rather than independent data. Consequently a ring homomorphism fixing $\bar{\mathbb{Q}}$ and moving $u$ to any other transcendental point of the same circle automatically intertwines conjugation, and no vanishing-coefficient statement over $\bar{\mathbb{Q}} \oplus \bar{\mathbb{Q}}u \oplus \bar{\mathbb{Q}}\bar u$ separates a candidate from an ordinary complex number placed there. This is formalised at <https://github.com/carlok/diaz-modulus-lean>. Any successful attack must therefore introduce information that is not a rational function of $u$ over $\bar{\mathbb{Q}}$ — which is exactly the methodological question Diaz raised alongside the conjecture and left open.
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   Open leaves beneath this node (24 September 2026): `normSq_transcendental_of_generic_conj_pair`, `recip_pi_not_log_real_gamma`, `recip_pi_not_log_imag_gamma`. The first sits under `norm_transcendental_of_generic_conj_pair`, which is **equivalent to the root** modulo Hermite–Lindemann, so the part of this subtree that runs through it is circular. The other two are the halves of the statement (S), and at least one of them holds (`recip_pi_not_log_real_or_imag`). `four_exponentials_trdeg_one`, listed here earlier as a leaf, is now proved.
--
--
--   The mission's live frontier is the set of nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'etude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Theor. Nombres Bordeaux 16 (2004), no. 3, 535-553, doi:10.5802/jtnb.459, section 5.1, p. 550; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer 2000, p. 399

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_modulus_conjecture : DiazModulusConjecture := by sorry
end DiazModulus
