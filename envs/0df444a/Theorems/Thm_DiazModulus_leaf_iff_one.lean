-- Prove2me | Theorems.Thm_DiazModulus_leaf_iff_one
-- name    : DiazModulus.leaf_iff_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:57:03.325876+00:00
-- url     : https://prove2.me/theorems/9f689eee-634e-4b2a-939a-045c452623d4
-- title:
--   The real-generic case is equivalent to one relation: t² + π² is transcendental
-- statement:
--   **Statement.** The left-hand side is, verbatim, the statement of the open node
--   `DiazModulus.diaz_of_exp_real_generic`: the real-generic case of Diaz's conjecture, where $e^{u}$
--   is real and $\neq 1$ and neither $\Re u$ nor $\Im u$ vanishes. This node says it is **equivalent
--   to a single relation in one real variable**:
--   $$\text{for every }t\neq 0\text{ with }e^{t}\text{ algebraic},\quad
--     t^{2}+\pi^{2}\text{ is transcendental.}$$
--   Equivalently: *the principal logarithm of a negative algebraic number of modulus $\neq 1$ has
--   transcendental modulus*, since $(\log b)^{2}+\pi^{2}=\lVert\operatorname{Log}(-b)\rVert^{2}$.
--   In particular the smallest instance, "is $\sqrt{(\log 2)^{2}+\pi^{2}}$ algebraic?", is not a
--   sample of the case --- the case has one real parameter $b$ and nothing else.
--
--   Two things are folded into this. First, the integer $k$ with $\Im u=k\pi$ carries no arithmetic:
--   if $t^{2}+k^{2}\pi^{2}$ were algebraic then $t/|k|$ is again a non-zero real logarithm of an
--   algebraic number --- $e^{t/|k|}$ is a real $|k|$-th root of $e^{t}$ --- and
--   $(t/|k|)^{2}+\pi^{2}$ is algebraic too. Second, "$e^{u}$ real" is "$\Im u\in\pi\mathbb{Z}$",
--   which is where $\pi^{2}$ enters.
--
--   **This is an equivalence, not a decomposition.** The right-hand side is the case restated, not a
--   weaker statement; it reduces nothing and creates no research work of its own. It is published
--   because the description is the useful object: it names what would have to be proved.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's: the equivalence is Theorem 3.5 of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). **No novelty is claimed.** The normal form is the closing clause of a torsion dichotomy --- $u_{0}:=u/s=\ell+i\pi$,
--   $u_{0}\overline{u_{0}}=\ell^{2}+\pi^{2}$ --- which, with the statement that the torsion branch is one
--   relation and a polar normal form of the conjecture, he states for the larger torsion branch $\Im u\in\pi\mathbb{Q}$,
--   hence subsuming the integer case here. These three statements are unpublished, and none of them is on the board:
--   `Diaz.torsion_dichotomy` publishes only the (ii)$\Leftrightarrow$(iii) equivalence. Nothing in
--   the mathematics is new; what this node adds is only the machine-checked chain from the platform's
--   own statement of the case to it, and that is small.
--
--   **Where the difficulty sits.** Section 4 of the note, item (b) and the paragraph after it,
--   identifies the obstruction as **Waldschmidt's own open question**: the remark following Theorem
--   15.30 of *Diophantine Approximation on Linear Algebraic Groups*, that the homogeneous rational
--   quadratic theorem is available in transcendence degree one and "it would be interesting to extend
--   this statement to nonhomogeneous quadratic polynomials", the model case being the transcendence of
--   $e^{\lambda^{2}}$, with $e^{\pi^{2}}$ still open --- p. 593 of the book. The board shows the
--   same wall in miniature: `Diaz.salem_quartic_relations` settles the homogeneous form
--   $At^{2}+Bts+Cs^{2}=0$ for $t$ real, $s$ purely imaginary and rational $A,B,C$; this node is the
--   inhomogeneous instance $(A,B,C)=(1,0,-1)$ with right-hand side an algebraic number instead of $0$.
--
--   **Proof.** No transcendence input is used; the content is the change of variables
--   $u=t+ik\pi$ and a descent in $k$. Forward: given the case, the witness $u=t+i\pi$ has
--   $\lVert u\rVert^{2}=t^{2}+\pi^{2}$, real exponential $-e^{t}$ which is algebraic and $\neq 1$,
--   and non-zero real and imaginary parts. Backward: $e^{u}$ real forces $\sin(\Im u)=0$, so
--   $\Im u=k\pi$ with $k\neq 0$; then $e^{\Re u}=\pm e^{u}$ is algebraic and
--   $\lVert u\rVert^{2}=(\Re u)^{2}+k^{2}\pi^{2}$ is algebraic; put $s=\Re u/|k|$, whose
--   exponential is algebraic by `Diaz.exp_ratMul_isAlgebraic` at the rational $1/|k|$, and
--   $s^{2}+\pi^{2}=\lVert u\rVert^{2}/k^{2}$ is algebraic --- contradicting the one relation at
--   $s$.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 3.5. Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem leaf_iff_one :
    (∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
        u.im ≠ 0 → Complex.exp u ≠ 1 → u.re ≠ 0 → Transcendental ℚ (Complex.exp u))
      ↔ (∀ t : ℝ, t ≠ 0 → IsAlgebraic ℚ ((Real.exp t : ℝ) : ℂ) →
          Transcendental ℚ ((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ)) := by sorry
end DiazModulus
