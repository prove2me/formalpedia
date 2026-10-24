-- Prove2me | Theorems.Thm_FiniteFieldKakeya_mixed_line_jet_detection
-- name    : FiniteFieldKakeya.mixed_line_jet_detection
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T06:30:57.458833+00:00
-- url     : https://prove2.me/theorems/2ffb1041-896f-4e01-b4f9-3d276bd42f29
-- title:
--   Mixed-line jet detection for anisotropic polynomial spaces (Bukh–Chao Lemma 9)
-- statement:
--   Let $F$ be a finite field of cardinality $q$, let $d,r,r'$ be natural numbers with $0<r\le r'$, and choose an arbitrary affine-line anchor $a(b)\in F^{d+1}$ for each $b\in F^d$. Let $P$ be a polynomial in $d+1$ variables. Assume every monomial $X^\alpha$ in its support satisfies
--
--   $$\sum_{j=1}^d\alpha_j<rq,\qquad |\alpha|<r'q.$$
--
--   For every transverse multi-index $i$ with $|i|<r$, restrict the Hasse derivative $H_{(0,i)}P$ to the line $a(b)+t(1,b)$. Suppose that at every $t\in F$ its Taylor coefficients of orders $j<r'-\lfloor |i|/q\rfloor$ vanish, for every $b\in F^d$. Then $P$ is the zero polynomial.
--
--   This is the polynomial detection step for the sharp finite-field Kakeya bound. The theorem allows any integer $r'\ge r$, including the parameter used in the paper, and retains $d=0$. It requires neither a Kakeya hypothesis on the anchors nor a characteristic-zero assumption. The paper's distinguished last coordinate is relabeled as coordinate zero.
-- source:
--   Bukh and Chao, Sharp density bounds on the finite field Kakeya problem, arXiv:2108.00074v2, Discrete Analysis 2021:26, p. 5, Lemma 9, using Lemma 7 (p. 4). Generalization: the paper specializes r′=(2−1/q)r; this statement allows any natural r′≥r with the same degree and mixed-jet thresholds. Necessary detection input for public sharp Kakeya target448b0e69-57fd-4028-ab8b-07964b7b3c5b.

import Mathlib
import Definitions.Def_KakeyaPolynomialMethods

theorem FiniteFieldKakeya.mixed_line_jet_detection {F : Type*} [Field F] [Fintype F]
    (d r rp : ℕ) (hr : 0 < r) (hrrp : r ≤ rp)
    (a : (Fin d → F) → (Fin (d+1) → F)) (P : MvPolynomial (Fin (d+1)) F)
    (hsupport : ∀ α ∈ P.support,
      (∑ j : Fin d, α j.succ) < r * Fintype.card F ∧
      α.sum (fun _ e => e) < rp * Fintype.card F)
    (hjet : ∀ i : Fin d →₀ ℕ, i.sum (fun _ e => e) < r →
      ∀ b : Fin d → F, ∀ t : F, ∀ j : ℕ,
      j < rp - i.sum (fun _ e => e) / Fintype.card F →
      (Polynomial.taylor t (KakeyaPolynomialMethods.lineMap (a b) (Fin.cons 1 b)
        (KakeyaHasse.hasse (i.cons 0) P))).coeff j = 0) : P = 0 := by sorry
