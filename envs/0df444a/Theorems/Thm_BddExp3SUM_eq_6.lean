-- Prove2me | Theorems.Thm_BddExp3SUM_eq_6
-- name    : BddExp3SUM.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:59:33.529754+00:00
-- url     : https://prove2.me/theorems/5d13792a-8552-498e-aed1-f8b666762c7c
-- title:
--   (6): $K(\ker\pi)\subseteq B\cong\mathbb F_p^q$, $|B|=D$, and the split $B=B_1\times B_2$
-- statement:
--   For every choice of rows, if $\pi(x)=0$ then $K(x)$ lies in
--
--   $$B=\{0\}\times\{0\}^k\times((M/p)\mathbb Z_M)^q.$$
--
--   Moreover $B\cong\mathbb F_p^q$ as groups, $|B|=p^q=D$, and $B$ splits as $B_1\times B_2$ with $|B_1|=p^{\lceil q/2\rceil}$ and $|B_2|=p^{\lfloor q/2\rfloor}$: every element of $B$ is uniquely $\mu_1+\mu_2$.
--
--   This fixes the explicit middle group over which the support matrices are built.
--
--   Differences from the source:
--   - generalization: k, q, e, p from the certificate of a fixed subinstance → any k, q, e and any prime p ∣ M; reason: the claim is algebra about rows; the source’s parameters are a special case
--   - encoding: B = B₁ × B₂ → two subgroups of B with the given cardinalities and unique decomposition; reason: makes (µ₁, 0) and (0, µ₂) plain elements of the target of K
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), (6), p.4 (PDF p.5; the sentence starts on PDF p.4)

import Mathlib
import Definitions.Def_BddExp3SUM_Hash

namespace BddExp3SUM

/-- (6), p.4 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…):
`K(ker π) ⊆ B ≅ F_p^q`, `|B| = D = p^q`, and the split `B = B₁ × B₂` with dimensions `⌈q/2⌉`, `⌊q/2⌋`.

**Formalization Note.** `M/p` may be `1`, in which case `ZMod (M/p)` is the trivial ring. The split is
stated as: `B₁`, `B₂` have the right cardinalities, and each element of `B` is uniquely `μ₁ + μ₂`. -/
theorem eq_6 {M r e k q p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    (u : Fin (k + q) → Grp M r) :
    (∀ x : Grp M r, piHash hpM e u x = 0 → KHash e u x ∈ B M r e k q p) ∧
    Nonempty (B M r e k q p ≃+ (Fin q → ZMod p)) ∧
    Nat.card (B M r e k q p) = p ^ q ∧
    Nat.card (B₁ M r e k q p) = p ^ ((q + 1) / 2) ∧
    Nat.card (B₂ M r e k q p) = p ^ (q / 2) ∧
    ∀ w ∈ B M r e k q p, ∃! v : (B₁ M r e k q p) × (B₂ M r e k q p), (v.1 : KTarget M r e k q) + v.2 = w := by sorry

end BddExp3SUM
