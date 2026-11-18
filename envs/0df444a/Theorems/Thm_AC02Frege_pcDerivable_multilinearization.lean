-- Prove2me | Theorems.Thm_AC02Frege_pcDerivable_multilinearization
-- name    : AC02Frege.pcDerivable_multilinearization
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-17T06:03:22.535224+00:00
-- url     : https://prove2.me/theorems/5a8c97e9-7931-4f89-a952-6985282f3798
-- title:
--   Multilinearization preserves bounded-degree polynomial-calculus derivability
-- statement:
--   Let $F$ be a CNF on $n$ Boolean variables, and let polynomial calculus include the Boolean axioms $x_i^2+x_i$ over $\mathbb F_2$. If a formal polynomial $p$ is derivable in formal degree at most $D$, then its multilinearization is derivable within the same bound:
--   $$
--   p\text{ derivable in degree at most }D\quad\Longrightarrow\quad\operatorname{ML}(p)\text{ derivable in degree at most }D.
--   $$
--
--   Here multilinearization replaces every positive variable exponent by one and adds coefficients of coinciding monomials. This is the degree-preserving reduction recorded immediately before Fact 2.5, and is useful whenever Boolean-ring identities must be justified in formal polynomial calculus.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds, November 3, 2026, https://www.doc.ic.ac.uk/~itzamere/Syntactic_ACZTwo.pdf, Definitions 2.1–2.4 and Fact 2.5, printed pp.9–10. Supporting lemma for the formalization of Fact 2.5; the source records degree-preserving multilinearization immediately before the fact.

import Definitions.Def_AC02Frege_PC
open MvPolynomial

theorem AC02Frege.pcDerivable_multilinearization {n : ℕ}
    (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2))
    (hp : AC02Frege.PCDerivable F D p) :
    AC02Frege.PCDerivable F D (AC02Frege.ML p) := by sorry
