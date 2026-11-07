-- Prove2me | Theorems.Thm_BddExp3SUM_lemma_4
-- name    : BddExp3SUM.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:59:49.995409+00:00
-- url     : https://prove2.me/theorems/0c3933ea-0e4b-4838-9972-ddb2ea384ab9
-- title:
--   Lemma 4: $\langle u,v\rangle$ is uniform on the subgroup of order $d$; $\mathbb P[K(v)=0]=d^{-\ell}$, $\mathbb P[\pi(v)=0]=\gcd(d,p)^qd^{-\ell}\le Dd^{-\ell}$
-- statement:
--   If $v\in G$ has additive order $d$, a uniform row $u\in G$ maps $v$ uniformly onto the subgroup of $\mathbb Z_M$ of order $d$: there is a subgroup $A$ of order $d$ such that $\mathbb P[\langle u,v\rangle=a]=1/d$ for $a\in A$ and $0$ otherwise.
--
--   For nonzero $v\in H_e$ of order $d$ and independent uniform rows,
--
--   $$\mathbb P[K(v)=0]=d^{-\ell},\qquad\mathbb P[\pi(v)=0]=\gcd(d,p)^qd^{-\ell}\le Dd^{-\ell},$$
--
--   with $\ell=k+q$, $D=p^q$. Vectors outside $H_e$ have survival probability zero under both maps.
--
--   This is what lets the analysis treat every sum order separately.
--
--   Differences from the source:
--   - generalization: k, q, e, p from the certificate of a fixed subinstance → any k, q, any e ∈ 𝒟 and any prime p ∣ e; reason: the probabilities do not depend on the subinstance; the source’s parameters are a special case
--   - encoding: a uniform row on Z_M^r and independent rows → counting ratios on G and on Fin (k+q) → G; reason: the uniform law on a finite set
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 4, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_BddExp3SUM_Hash

namespace BddExp3SUM

/-- Lemma 4, p.4 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…).

**Formalization Note.** The first clause: for `v` of additive order `d`, there is a subgroup `A` of
`Z_M` of order `d` such that `⟨u, v⟩` takes each value of `A` with probability `1/d` and no other
value, for `u` uniform on `G`. The other clauses are for uniform rows `u : Fin (k + q) → G`. -/
theorem lemma_4 {M r k q e p : ℕ} [NeZero M] (he : e ∈ Dvs M) (hp : p.Prime) (hpe : p ∣ e)
    (hpM : p ∣ M) :
    (∀ v : Grp M r, ∃ A : AddSubgroup (ZMod M), Nat.card A = addOrderOf v ∧
      ∀ a : ZMod M,
        (a ∈ A → uniformProb (fun u : Grp M r => rowHom u v = a) = 1 / (addOrderOf v : ℝ)) ∧
        (a ∉ A → uniformProb (fun u : Grp M r => rowHom u v = a) = 0)) ∧
    (∀ v ∈ H M r e, v ≠ 0 →
      uniformProb (fun u : Fin (k + q) → Grp M r => KHash e u v = 0) =
        ((addOrderOf v : ℝ) ^ (k + q))⁻¹ ∧
      uniformProb (fun u : Fin (k + q) → Grp M r => piHash hpM e u v = 0) =
        (Nat.gcd (addOrderOf v) p : ℝ) ^ q * ((addOrderOf v : ℝ) ^ (k + q))⁻¹ ∧
      (Nat.gcd (addOrderOf v) p : ℝ) ^ q * ((addOrderOf v : ℝ) ^ (k + q))⁻¹ ≤
        (p : ℝ) ^ q * ((addOrderOf v : ℝ) ^ (k + q))⁻¹) ∧
    ∀ v : Grp M r, v ∉ H M r e →
      uniformProb (fun u : Fin (k + q) → Grp M r => KHash e u v = 0) = 0 ∧
      uniformProb (fun u : Fin (k + q) → Grp M r => piHash hpM e u v = 0) = 0 := by sorry

end BddExp3SUM
