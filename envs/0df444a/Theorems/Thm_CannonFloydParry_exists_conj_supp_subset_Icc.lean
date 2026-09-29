-- Prove2me | Theorems.Thm_CannonFloydParry_exists_conj_supp_subset_Icc
-- name    : CannonFloydParry.exists_conj_supp_subset_Icc
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-16T12:14:59.249918+00:00
-- url     : https://prove2.me/theorems/a8c6d7cf-5111-4ff4-958c-44d15bb0e0ff
-- title:
--   $[F,F]$ conjugates each of its elements into a prescribed dyadic interval
-- statement:
--   Fix dyadic rationals $a, b$ with $0 < a < b < 1$. Let $w \in F$ be trivial in a neighbourhood of $0$ and in a neighbourhood of $1$; by Theorem 4.1 these are exactly the elements of the commutator subgroup $[F,F]$.
--
--   Then there is an element $\varphi \in F$, itself trivial near $0$ and near $1$ (so $\varphi \in [F,F]$ as well), and reals $c, d$ with
--   $$a < c < d < b,$$
--   such that the conjugate $\varphi w \varphi^{-1}$ is supported inside $[c,d]$; that is, $\varphi w \varphi^{-1}$ fixes every point of $[0,1]$ outside $[c,d]$. The conclusion is phrased pointwise as: whenever $\varphi\big(w(\varphi^{-1}(z))\big) \neq z$ one has $c \le z \le d$.
--
--   This is the transitivity statement that the simplicity argument needs. Because $w$ is trivial near the two endpoints, its support is contained in some interval $[s,t] \subset (0,1)$; enlarging to dyadic endpoints and using the transitivity of $F$ on dyadic partitions of $[0,1]$, one builds $\varphi \in F$ which is the identity near $0$ and near $1$ and carries $[s,t]$ into a compact subinterval of $(a,b)$. Conjugation transports supports, $\operatorname{supp}(\varphi w \varphi^{-1}) = \varphi(\operatorname{supp} w)$, which gives the conclusion. The requirement $c > a$ and $d < b$ — strict containment, not merely support inside $(a,b)$ — is what later makes $\varphi w \varphi^{-1}$ trivial near the endpoints of $[a,b]$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Theorem 4.5, p. 230 (supporting step in the proof that the commutator subgroup of $F$ is simple)

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem exists_conj_supp_subset_Icc {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hda : IsDyadic a) (hdb : IsDyadic b)
    {w : UI ≃o UI} (hw : w ∈ F) (hw0 : TrivialNearZero w) (hw1 : TrivialNearOne w) :
    ∃ φ : UI ≃o UI, φ ∈ F ∧ TrivialNearZero φ ∧ TrivialNearOne φ ∧
      ∃ c d : ℝ, a < c ∧ c < d ∧ d < b ∧
        ∀ z : UI, (φ (w (φ.symm z)) : ℝ) ≠ (z : ℝ) → (z : ℝ) ∈ Set.Icc c d := by
  sorry

end CannonFloydParry
