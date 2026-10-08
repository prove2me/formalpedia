-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_lemma1_solution
-- name    : BesbesZeevi.SingleParam.lemma1_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:00:45.023703+00:00
-- url     : https://prove2.me/theorems/75d6c7ae-0ac9-4f4e-83cc-709edf15fc06
-- title:
--   Lemma 1 (solution of (5))
-- statement:
--   Let $\lambda\in\mathcal L(M,\underline K,\overline K,m)$ with $M,\underline K,m>0$, $\underline K\le\overline K$. Let $p^u\in[\underline p,\overline p]$ be any maximizer of $p\lambda(p)$ over $[\underline p,\overline p]$, $p^c\in[\underline p,\overline p]$ any minimizer of $|\lambda(p)-x/T|$ over $[\underline p,\overline p]$, and put $p^D=\max\{p^u,p^c\}$ and $T'=\min\{T,x/\lambda(p^D)\}$. Then the path that applies $p^D$ on $[0,T']$ and $p_\infty$ afterwards is feasible for the deterministic relaxation (5), and it is optimal:
--
--   $$
--   J^D(x,T\mid\lambda)=p^D\lambda(p^D)\,T'.
--   $$
--
--   This identifies the full-information benchmark with a single fixed price, which is what the learning algorithms try to approach.
--
--   **Formalization Note** Only the first sentence of Lemma 1 is formalized; its second sentence ($J^\pi\le J^D$ for every admissible policy) is not part of this item. On the class, $\lambda(p^D)>0$, so $x/\lambda(p^D)$ is a genuine quotient.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF p. 29), Lemma 1 (first assertion)

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_Model

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- Lemma 1, first assertion (Besbes–Zeevi 2009, p. 27): for `λ ∈ 𝓛`, the path that applies
`p^D = max {p^u, p^c}` on `[0, T']` and `p∞` afterwards, `T' = min {T, x/λ(p^D)}`, is
feasible for (5) and attains its value `J^D(x, T | λ) = p^D λ(p^D) T'`. Here `p^u` is any
maximizer of `p λ(p)` and `p^c` any minimizer of `|λ(p) - x/T|` on `[p̲, p̄]`. -/
theorem lemma1_solution (D : Market) (M KLo KHi m : ℝ) (hM : 0 < M) (hKLo : 0 < KLo)
    (hK : KLo ≤ KHi) (hm : 0 < m) (f : ℝ → ℝ) (hf : InClass D M KLo KHi m f)
    (pu pc : ℝ) (hpu : pu ∈ Set.Icc D.pLo D.pHi)
    (hpu_max : IsMaxOn (fun p => p * f p) (Set.Icc D.pLo D.pHi) pu)
    (hpc : pc ∈ Set.Icc D.pLo D.pHi)
    (hpc_min : IsMinOn (fun p => |f p - D.x / D.T|) (Set.Icc D.pLo D.pHi) pc) :
    Feasible D f D.x
        (fun s => if s ≤ min D.T (D.x / f (max pu pc)) then max pu pc else D.pOff) ∧
      detValue D f D.x = max pu pc * f (max pu pc) * min D.T (D.x / f (max pu pc)) := by sorry

end BesbesZeevi.SingleParam
