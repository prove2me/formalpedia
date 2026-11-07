-- Prove2me | Theorems.Thm_AC02Frege_fact_2_5_multiplication_rule
-- name    : AC02Frege.fact_2_5_multiplication_rule
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:30.063179+00:00
-- url     : https://prove2.me/theorems/0ca2bd56-533e-4885-b430-d28510e1f6c0
-- title:
--   Fact 2.5 — the multiplication rule for $C_D$
-- statement:
--   Let $F$ be a CNF in the variables $y_1,\dots,y_n$ and $C_D$ its degree-$D$ PC consequence space. For multilinear $u,v$,
--   $$
--   u\in C_D,\quad \deg_y u+\deg_y v\le D\ \Longrightarrow\ uv\in C_D ,
--   $$
--   where $uv$ is the multilinear product.
--
--   This is the closure property that the whole argument uses to multiply known consequences of $F$ by low-degree polynomials.
--
--   Differences from the source:
--   - generalization: F of width w(F) ≤ D (standing assumption of Definition 2.4) → every CNF F, no width hypothesis; reason: the multiplication and multilinearization steps use only Boolean axioms of degree at most deg u + deg v ≤ D, so the statement specializes to the source
--   - encoding: uv a product of functions, deg_y the degree → ML (u * v) with v multilinear, totalDegree; reason: Definition 2.1; same instances
--   - encoding: C_D: multilinear p with a PC derivation of 1 + p = 1 in degree ≤ D → multilinear p with p = 0 or p a line of a PCNonBool.IsDerivation (identity reduction) from the clause complements and y_i² + y_i, every line of totalDegree ≤ D; reason: the complement 0 of 1 = 1 is trivially derivable; every other polynomial is derivable in one system iff in the other
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Fact 2.5, (2), p.10

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Fact 2.5, (2), p.10: the multiplication rule for `C_D`,
`u ∈ C_D, deg_y u + deg_y v ≤ D ⟹ uv ∈ C_D`.

**Formalization Note** `uv` is the multilinear product `ML (u * v)`; `v` is multilinear (a
function on the cube). Stated for every CNF `F`, without the standing assumption `w(F) ≤ D` of
Definition 2.4. -/
theorem fact_2_5_multiplication_rule {n : ℕ} (F : CNF (Fin n)) (D : ℕ)
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : u ∈ CD F D) (hv : IsMultilinear v)
    (hdeg : u.totalDegree + v.totalDegree ≤ D) : ML (u * v) ∈ CD F D := by sorry

end AC02Frege
