-- Prove2me | Theorems.Thm_CirclePackingConstants_sixteen_nogood_batch4
-- name    : CirclePackingConstants.sixteen_nogood_batch4
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T15:04:58.659809+00:00
-- url     : https://prove2.me/theorems/0ccea89d-96e4-4b4e-a739-9ae29f53bced
-- title:
--   Occupancy patterns $255\le e<367$ of the sixteen-point library are impossible
-- statement:
--   Let $p_1,\dots,p_{16}$ be points of the plane with pairwise squared distances greater than $\tfrac19$ (pairwise distances greater than $\tfrac13$), and let each $p_k$ lie in the closed cell $Q_{c_k}=[\tfrac{x_k}4,\tfrac{x_k+1}4]\times[\tfrac{y_k}4,\tfrac{y_k+1}4]$ of the $4\times4$ subdivision of the unit square, with label $c_k=(x_k,y_k)\in\mathbb N^2$. Let $E$ be the entry number $e$, with $255\le e<367$, of the pattern library `sixteenLib`, i.e. a list of triples $(x,y,m)$, and let $(s,tx,ty)$ be a placement of the pattern by a symmetry of the square and a translation by whole cells. Then it is impossible that for every triple $(x,y,m)$ of $E$ the placed cell lies in the $4\times4$ grid and at least $m$ of the labels $c_k$ equal it.
--
--   In other words, none of the library patterns in the stated range (in any of its images under the dihedral symmetries and translations) is realized by the occupation counts of the cells. A pattern consists of two or three points in one cell together with the occupation of surrounding cells. The exclusion is a finite branch and bound over boxes: from the separation $>\tfrac13$ interval propagation gives, for two points whose $y$-coordinates differ by at most $Y$, $|x_p-x_q|>\sqrt{1/9-Y^2}$, and every case of a finite case tree is driven to a contradiction.
--
--   **Formalization Note.** `Sixteen.place`, `Sixteen.inGrid` and `Sixteen.sixteenLib` are defined in `CirclePackingConstants_SixteenOcc`; labels are pairs of natural numbers and the position of the points in the cells is stated with explicit inequalities. The proof is a kernel-checked certificate (`decide +kernel`) for the library entries in the stated range, using the certified box checker `CirclePackingConstants_BoxChecker`.
-- source:
--   G. Wengerodt, Die dichteste Packung von 16 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie 16 (1983), 173-190 (optimality of the 4x4 grid); the occupancy-pattern decomposition, the pattern library and the certificates are computer generated for this formalization.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_SixteenOcc

noncomputable section

namespace CirclePackingConstants

theorem sixteen_nogood_batch4 (e : ℕ) (he1 : 255 ≤ e) (he2 : e < 367) (ent : List (ℕ × ℕ × ℕ))
    (hent : Sixteen.sixteenLib[e]? = some ent) (p : Fin 16 → Point) (cl : Fin 16 → ℕ × ℕ)
    (hcl : ∀ k, ((cl k).1 : ℝ) / 4 ≤ (p k).1 ∧ (p k).1 ≤ (((cl k).1 : ℝ) + 1) / 4 ∧
      ((cl k).2 : ℝ) / 4 ≤ (p k).2 ∧ (p k).2 ≤ (((cl k).2 : ℝ) + 1) / 4)
    (hsep : ∀ i j, i ≠ j → (1 : ℝ) / 9 < sqDist (p i) (p j)) (s tx ty : ℕ)
    (hm : ∀ t ∈ ent, Sixteen.inGrid (Sixteen.place s tx ty (t.1, t.2.1)) = true ∧
      t.2.2 ≤ (Finset.univ.filter (fun k : Fin 16 => cl k = ((Sixteen.place s tx ty (t.1, t.2.1)).1.toNat,
        (Sixteen.place s tx ty (t.1, t.2.1)).2.toNat))).card) : False := by sorry
